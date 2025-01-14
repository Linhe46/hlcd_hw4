#include "common.h"
#include <minisat/core/Solver.h>
#include <queue>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <cmath>
#include <limits>
#include <utility>
#include <iostream>

using namespace std;
// topological sorting
void topo_sort(int n, vector<int> &topo_order, const vec2d<int>& uses, const vec2d<int>& deps){
    // uses means out_edge, deps means in_edge
    vector<int> indeg(n);
    topo_order.clear();
    for(int i = 0; i < n; i++)
        indeg[i] = deps[i].size();
    queue<int> q;
    for(int i = 0; i < n; i++)
        if(indeg[i] == 0)
            q.push(i);
    
    while(!q.empty()){
        int u = q.front();
        q.pop();
        topo_order.push_back(u);
        for(auto v: uses[u]){
            indeg[v]--;
            if(indeg[v] == 0)
                q.push(v);
        }
    }
}

bool is_comb(Stmt* stmt){
    return stmt->op->latency == 0;
}

// naive check: delay until no resource conflict
void check_resource(int& sched_cycle, const std::string& op_name, int op_limit, int l_v,
        const unordered_map<std::string, unordered_map<int, int>>& clock_busy){
    int cnt = 0;
    while(1){
        bool flag = 1;
        for(int ck = sched_cycle + cnt; ck < sched_cycle + cnt + l_v; ck++){
            if(clock_busy[op_name][ck] + 1 > op_limit){
                flag = 0;
                break;
            }
        }
        if(flag){
            sched_cycle += cnt;
            break;
        }
        cnt++;
    } 
}

int asap(DFG* dfg, const vector<Op*>& ops, double clock_period){
    // get topo sort
    vec2d<int> uses,deps;
    get_deps_and_uses(dfg, deps, uses);
    vector<int> topo_order{};
    int n = dfg->stmts.size();
    topo_sort(n, topo_order, uses, deps);
    // schedule
    int tot_latency = 0;
    unordered_map<int, double> clock_delay;
    unordered_map<std::string, unordered_map<int, int>> clock_busy; // check if over limit
    for(auto v: topo_order){
        cout<<"scheduling stmt id: "<<v<<endl;
        auto stmt_v = dfg->stmts[v];
        int l_v = stmt_v->op->latency;
        int sched_cycle = 0;
        if(deps[v].size() == 0){
            sched_cycle = 1;
            check_resource(sched_cycle, stmt_v->op->name, stmt_v->op->limit, l_v, clock_busy);
            stmt_v->start_cycle = sched_cycle;
        }
        else {
            for(auto u: deps[v]){
                auto stmt_u = dfg->stmts[u];
                int l_u = stmt_u->op->latency;
                cout<<"checking "<<v <<" denpends on "<<u<<" ..."<<endl;
                // combinational logic has no limit
                if(is_comb(stmt_v)){
                    // schedule by delay
                    int last_cycle_u = is_comb(stmt_u) ? stmt_u->start_cycle : stmt_u->start_cycle + l_u - 1;
                    int cnt = 0;
                    while(clock_delay[last_cycle_u + cnt] + stmt_v->op->delay > clock_period){
                        cnt++;
                    }
                    sched_cycle = max(stmt_v->start_cycle, last_cycle_u + cnt);
                }
                // temporal logic: check limit
                else{
                    // schedule by first feasible cycle
                    sched_cycle = max(stmt_v->start_cycle, stmt_u->start_cycle + (is_comb(stmt_u) ? 1 : l_u));
                    check_resource(sched_cycle, stmt_v->op->name, stmt_v->op->limit, l_v, clock_busy);
                }
                stmt_v->start_cycle = sched_cycle; // allocate scheduled cycle id
            }
        }
        // update v's last cycle delay
        int last_cycle_v = stmt_v->start_cycle + (is_comb(stmt_v) ? 0 : l_v - 1); 
        clock_delay[last_cycle_v] += stmt_v->op->delay;
        // update v's busy cycles if has a limit
        if(stmt_v->op->limit != -1){
            for(int d_ck=0; d_ck < l_v; d_ck++)
                clock_busy[stmt_v->op->name][stmt_v->start_cycle + d_ck]++;
        }
        // update total latency
        tot_latency = max(tot_latency, last_cycle_v);
        cout<<"scheduling stmt id "<<v<<" at cycle: "<< stmt_v->start_cycle<<endl;
    }
    cout<<"delay at each cycle: "<<endl;
    for(auto delay: clock_delay)
        cout<< "cycle "<<delay.first << " has delay: " << delay.second<<endl;
    cout<<"resource at each cycle: "<<endl;
    for(auto busy: clock_busy){
        cout<<busy.first<<": ";
        for(auto t_busy: busy.second)
            cout<< t_busy.first <<"->" << t_busy.second<<' ';
    }
    cout<<endl;
    return tot_latency;
}

struct Cons{
    // x_{v} - x{u} <= c
    // equals an edge from u to v with weight c
    int v, u;
    int c;
    Cons(int v, int u, int c): v(v), u(u), c(c){}
};

struct SDCSolver{
    int n; // num of vals
    vector<Cons*> constraints; 
    vector<int> dist;
    vector<vector<pair<int, int>>> edges; // for inc_solver's dijkstra

    SDCSolver(int n): n(n){
        dist.resize(n, 0);
        edges.resize(n, {});
    }
    ~SDCSolver(){
        for(auto cons_ptr: constraints)
            delete cons_ptr;
    }

    void addConstraint(int v, int u, int c){
        Cons* cons_ptr = new Cons(v, u, c);
        constraints.push_back(cons_ptr);
        edges[u].push_back({v, c}); // add edge
    }
    // initial solve by Bellman-Ford algorithm
    bool initial_solve(){
        for(int i = 0; i < n-1; i++){
            bool updated = false;
            for(auto cons_ptr: constraints){
                int u = cons_ptr->u;
                int v = cons_ptr->v;
                int c = cons_ptr->c;
                if(dist[u] + c < dist[v]){
                    dist[v] = dist[u] + c;
                    updated = true;
                }
            }
            if(!updated) break; // early break
        }
        // negative cycle check
        for(auto cons_ptr: constraints){
            int u = cons_ptr->u;
            int v = cons_ptr->v;
            int c = cons_ptr->c;
            if(dist[u] + c < dist[v])
                return false;
        }
        return true;
    }

    bool inc_solve(int v, int u, int c){
        vector<int> dist_new = dist;
        vector<int> dist_v(n, numeric_limits<int>::max());
        dist_v[v] = 0;
        auto cmp = [&dist_v](int u, int v) { return dist_v[u] > dist_v[v]; };
        priority_queue<int, vector<int>, decltype(cmp)> pq(cmp);
        pq.push(v);
        while(!pq.empty()){
            int cur_node = pq.top();
            pq.pop();
            int d = dist_v[cur_node] + dist[cur_node] - dist[v]; // edmond_karp length
            if(dist[u] + d + c < dist[cur_node]){
                if(cur_node == u)
                    return false; // update u, negative cycle!
                dist_new[cur_node] = dist[u] + d + c; // update solution
                for(auto& pair: edges[cur_node]){
                    int w = pair.first; // to_node
                    int k = pair.second; // weight
                    int ek_d = k + dist[cur_node] - dist[w]; 
                    if(dist_v[cur_node] + ek_d < dist_v[w]){
                        dist_v[w] = dist_v[cur_node] + ek_d;
                        pq.push(w);
                    }
                }
            }
        }
        addConstraint(v, u, c); // add the constraint
        dist = std::move(dist_new); // update solution
        return true;
    }

    void printSolutioin(const std::string& info = "SDC solution"){
        cout<<info<<endl;
        for(int i = 0; i < n; i++)
            cout<<"variable "<< i+1 <<": " <<dist[i]<<endl;
    }
};

void get_dependent_constraints(SDCSolver* sdc_solver, DFG *dfg, const vec2d<int>& deps){
    // opi depends on opj
    for(int i = 0; i < deps.size(); i++){
        auto& stmt_i = dfg->stmts[i];
        // opi is combinational
        if(is_comb(stmt_i)){
            for(auto j: deps[i]){
                auto& stmt_j = dfg->stmts[j];
                // at least 0/lat_j-1 cycle
                // comb-comb/temp-comb NEED delay check
                sdc_solver->addConstraint(j, i, is_comb(stmt_j) ? 0 : 1 - stmt_j->op->latency); // xj <= xi
            }
        }
        // opi is temporal
        else{
            for(auto j: deps[i]){
                auto& stmt_j = dfg->stmts[j];
                // decided by latency
                // xi - xj >= Lat_j -> xj - xi <= -Lat_j, comb_lat is 1 for temp
                sdc_solver->addConstraint(j, i, is_comb(stmt_j) ? -1 : -stmt_j->op->latency);
            }
        }
    }
}

unordered_set<int> dfs_cp(int s, double cur_delay, DFG* dfg, double clock_period, const vec2d<int>& uses){
    unordered_set<int> res{};
    for(auto k: uses[s]){
        auto stmt_k = dfg->stmts[k];
        if(!is_comb(stmt_k)) // *-temp, no delay check
            continue;
        double k_delay = stmt_k->op->delay;
        if(clock_period - cur_delay < k_delay) // find a leaf
            res.insert(k);
        else{
            auto sub_set = dfs_cp(k, cur_delay + k_delay, dfg, clock_period, uses);
            res.insert(sub_set.begin(), sub_set.end());
        }
    }
    return res;
}

void get_chaining_constraints(SDCSolver* sdc_solver, DFG *dfg, const vec2d<int>& uses,
    const vector<int>& topo_order, double clock_period){
    for(auto i: topo_order){
        auto stmt_i = dfg->stmts[i];
        // search the critical path
        unordered_set<int> next_cycle_set = dfs_cp(i, stmt_i->op->delay, dfg, clock_period, uses);
        for(auto j: next_cycle_set) // xj - xi >= t, t = 1 for comb, lat_i for temp
            sdc_solver->addConstraint(i, j, is_comb(stmt_i) ? -1 : -stmt_i->op->latency); // 
    }
}

// a naive linear order from topo_Sort
void get_linear_order_topo(DFG *dfg, const vector<int>& topo_order, unordered_map<string, vector<int>>& linear_order){
    for(auto id: topo_order){
        if(dfg->stmts[id]->op->limit == -1) // no limit ops
            continue;
        auto op_name = dfg->stmts[id]->op->name;
        linear_order[op_name].push_back(id);
    }
}

void get_resource_constraints(SDCSolver* sdc_solver, DFG* dfg, const unordered_map<string, vector<int>>& linear_order){
    for(const auto& pair: linear_order){
        auto& order = pair.second;
        auto limit = dfg->stmts[order[0]]->op->limit;
        auto latency = dfg->stmts[order[0]]->op->latency;
        // grouping and get constraints
        // x_{i+limit} - x_i >= latancy
        if(limit >= order.size())
            continue;
        for(int i = 0; i < limit; i++){
            for(int j = 0; j < order.size()/limit; j++){
                int idx_j = i + j * limit;
                int idx_k = idx_j + limit;
                if(idx_k >= order.size())
                    continue;
                int x_j = order[idx_j];
                int x_k = order[idx_k];
                sdc_solver->addConstraint(x_j, x_k, -latency);
                cout<<pair.first<<"with size "<<order.size()<< ": x"<<x_j <<" - x"<<x_k <<" <= "<< -latency<<endl;
            }
        }
    }
}

void schedule(DFG *dfg, const vector<Op*> &ops, double clock_period) {
    cout<<"-----------my schedule begin----------------\n";

    int n = dfg->stmts.size();
    SDCSolver* sdc_solver = new SDCSolver(n);

    vec2d<int> uses,deps;
    get_deps_and_uses(dfg, deps, uses);
    vector<int> topo_order{};
    topo_sort(n, topo_order, uses, deps);

    get_dependent_constraints(sdc_solver, dfg, deps);
    int dep_cons_num;
    cout<<"dependent constraints: \n";
    for(auto cons_ptr: sdc_solver->constraints){
        int u=cons_ptr->u;
        int v=cons_ptr->v;
        int c=cons_ptr->c;
        cout<< "x"<<v <<" - x"<<u<<" <= "<< c<<endl;
        dep_cons_num = sdc_solver->constraints.size();
    }
    cout<<"chaining constraints: \n";
    get_chaining_constraints(sdc_solver, dfg, uses, topo_order, clock_period);
    for(int i = dep_cons_num; i < sdc_solver->constraints.size(); i++){
        auto cons_ptr = sdc_solver->constraints[i];
        int u=cons_ptr->u;
        int v=cons_ptr->v;
        int c=cons_ptr->c;
        cout<< "x"<<v <<" - x"<<u<<" <= "<< c<<endl;
    }
    cout<<"resource constraints: \n";
    unordered_map<string, vector<int>> linear_order;
    get_linear_order_topo(dfg, topo_order, linear_order);
    get_resource_constraints(sdc_solver, dfg, linear_order);

    cout << "sdc_initial solution "<< endl;
    sdc_solver->initial_solve();

    auto& res = sdc_solver->dist;
    auto min_ele_abs = abs(*min_element(res.begin(), res.end()));
    for(int i = 0; i < n; i++){
        cout<<i<<" is at " << res[i] + min_ele_abs + 1<<endl;
    }
    for(int i = 0; i < n; i++){
        dfg->stmts[i]->start_cycle = res[i] + min_ele_abs + 1;
    }

    delete sdc_solver;
    cout<<"---------my schedule end-------------------\n";
} 
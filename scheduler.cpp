#include "common.h"
#include <minisat/core/Solver.h>
#include <queue>
#include <unordered_map>
#include <cmath>
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
    for(auto v: topo_order){
        cout<<"scheduling stmt id: "<<v<<endl;
        auto stmt_v = dfg->stmts[v];
        int l_v = stmt_v->op->latency;

        if(deps[v].size() == 0)
            stmt_v->start_cycle = 1;
        else {
            int sched_cycle = 0;
            for(auto u: deps[v]){
                auto stmt_u = dfg->stmts[u];
                int l_u = stmt_u->op->latency;
                cout<<"checking "<<v <<" denpends on "<<u<<" ..."<<endl;
                if(is_comb(stmt_v)){
                    // schedule by delay
                    int last_cycle_u = is_comb(stmt_u) ? stmt_u->start_cycle : stmt_u->start_cycle + l_u - 1;
                    int cnt = 0;
                    while(clock_delay[last_cycle_u + cnt] + stmt_v->op->delay > clock_period){
                        cnt++;
                    }
                    sched_cycle = max(stmt_v->start_cycle, last_cycle_u + cnt);
                }
                else{
                    // schedule by first feasible cycle
                    sched_cycle = max(stmt_v->start_cycle, stmt_u->start_cycle + (is_comb(stmt_u) ? 1 : l_u));
                }
                stmt_v->start_cycle = sched_cycle; // allocate scheduled cycle id
            }
        }
        // update v's last cycle delay
        int last_cycle_v = stmt_v->start_cycle + (is_comb(stmt_v) ? 0 : l_v - 1); 
        clock_delay[last_cycle_v] += stmt_v->op->delay;
        // update total latency
        tot_latency = max(tot_latency, last_cycle_v);
        cout<<"scheduling stmt id "<<v<<" at cycle: "<< stmt_v->start_cycle<<endl;
    }
    cout<<"delay at each cycle: "<<endl;
    for(auto delay: clock_delay)
        cout<< "cycle "<<delay.first << " has delay: " << delay.second<<endl;
    return tot_latency;
}

void schedule(DFG *dfg, const vector<Op*> &ops, double clock_period) {
    /*for(auto stmt_ptr: dfg->stmts)
        stmt_ptr->start_cycle = 1;
    (dfg->stmts.back())->start_cycle = 2;
    for(auto stmt_ptr: dfg->stmts){
        for(auto stmt_ins_ptr:stmt_ptr->ins)
            std::cout<<stmt_ins_ptr->op->name<<' ';
        std::cout<<'\n';
    }*/
    for(auto op_ptr:ops){
        std::cout<<op_ptr->name<<' ';
    }
    cout<<'\n'<<"clock period is: "<<clock_period<<'\n';
    cout << "dfg_memory_num is " << dfg->num_memory << '\n';
    asap(dfg, ops, clock_period);

    
    cout<<"schedule result is: ";
    for(auto stmt: dfg->stmts){
        cout<<stmt->start_cycle<<' ';
    }
    cout<<endl;
    /*for(int i = 0; i < uses.size(); i++){
        cout<<"stmt " <<i << " is used by: ";
        for(auto id: uses[i])
            cout<<id<<' ';
        cout<<'\n';
    }
    for(int i = 0; i < deps.size(); i++){
        cout<<"stmt " <<i << " depend on: ";
        for(auto id: deps[i])
            cout<<id<<' ';
        cout<<'\n';
    }*/
}
/*
main.cpp
AIM- to find and display all spanning trees of a given graph in increasing order of total cost
     (cost of a spanning tree= sum of weights of all edges in the ST)
      graph is WEIGHTED AND UNDIRECTED
Created by PRACHI GARG on 21/03/18.
Copyright © 2018 PRACHI GARG. All rights reserved.
*/
//abbreviation st stands for spanning tree
//vertices are in the form of numbers from 0 to V-1
//we start finding spanning trees from the 0th vertex

#include <iostream>
#include <map>
#include <list>
#include <queue>
#include <string>
using namespace std;

vector<pair<int, vector<pair<int, int>>>> ans_vector;
int min_cost_till_now=INT_MAX;// this is to keep a track of the next spanning tree with least cost
int no_of_vert=0;

//implementing graph using adjacency matrix
class graph{
public:
    int Vertex;
    int adj_mat[20][20];
    graph()
    {
        for(int i=0;i<Vertex;i++)
            for(int j=0;j<Vertex;j++)
                adj_mat[i][j]=0;
    }
    void add_edge(int u, int v, int weight)
    {
        adj_mat[u][v]=adj_mat[v][u]=weight;
    }
    void print()
    {
        for(int i=0;i<Vertex;i++){
            for(int j=0;j<Vertex;j++)
                cout<<adj_mat[i][j]<<" ";
            cout<<endl;
        }
    }
};

//1 partition is stored in this data structure
struct part
{
    int cost_st;
    vector<pair<int, int>> spanning;
    vector<pair<int, int>> inc_ed;
    vector<pair<int, int>> exc_ed;
};

vector<part> partitions;//stores all partitions
vector<pair<int, int>> current_span;//stores current spanning tree being formed by Prim_MST() or Prim_ST()

bool is_cycle(int mat[20][20],int src, int V)//checking if graph formed is cyclic or not
{
    map<int,bool> visited;
    queue<int> traverse;
    map<int,int> parent;
    parent[src]=src;
    visited[src]=true;
    traverse.push(src);
    while(!traverse.empty())
    {
        int node=traverse.front();
        traverse.pop();
        for(int i=0;i<V;i++)
            if(mat[node][i]>0)
            {
                if(!visited[i])
                {
                    traverse.push(i);
                    visited[i]=true;
                    parent[i]=node;
                }
                else if(visited[i]==true && i!=parent[node])
                    return 1;//cycle
            }
    }
    return 0;
}

int find_min_key(int arr[20], int V, vector<bool> mstset)
{
    int min_key=INT_MAX, min_index=-1;
    for(int i=0;i<V;i++)
    {
        if(arr[i]<min_key && mstset[i]==false){
            min_key=arr[i];
            min_index=i;
        }
    }
    return min_index;
}

/* Prim's implementation to find the MST of the graph
 Also, this function has been designed to return an empty edges vector if the graph passed to it is disconnected
 his is based on the idea- if we get the next minimum key as INT_MAX even if that vertex has not been included into mst, then graph is disconnected.
 */
int Prim_MST(int adj_mat[20][20], int V)
{
    current_span.clear();
    vector<pair<int, int>> mst_edges;
    int parent[V];
    int key[V];
    int tot_cost=0;
    vector<bool> mstset(V);
    for(int i=0;i<V;i++)
    {
        key[i]=INT_MAX;
        mstset[i]=false;
    }
    
    key[0]=0;
    parent[0]=-1;
    for(int c=0;c<V-1;c++)
    {
        int u=find_min_key(key, V, mstset);
        if(u==-1)
        {
            return -1;
        }
        mstset[u]=true;
        for(int v=0;v<V;v++)
        {
            if(adj_mat[u][v] && mstset[v]==false && adj_mat[u][v]< key[v])
            {
                parent[v]=u;
                key[v]=adj_mat[u][v];
            }
        }
    }
    //MST HAS BEEN FORMED
    for(int i=1;i<V;i++){
        int x=parent[i];
        tot_cost+=adj_mat[x][i];
        //cout<<x<<"->"<<i<<endl;
        current_span.push_back(make_pair(x, i));
    }
    return tot_cost;
}


//SPECIALISED PRIM'S ALGORITHM - to return spanning tree according to the partion
int Prim_ST(graph G, vector<pair<int,int>> include_edges, vector<pair<int,int>> exclude_edges)
{
    int V=G.Vertex;
    int new_mat[20][20];
    int mat_cycle[20][20];
    for(int i=0;i<V;i++)
        for(int j=0;j<V;j++)
            mat_cycle[i][j]=0;
    
    for(int i=0;i<V;i++)
        for(int j=0;j<V;j++)
            new_mat[i][j]=G.adj_mat[i][j];
    
    int u1,v1;
    for(vector<pair<int, int>>::iterator it=exclude_edges.begin(); it!=exclude_edges.end();it++)
    {
        u1=(*it).first;
        v1=(*it).second;
        new_mat[u1][v1]=new_mat[v1][u1]=INT_MIN;
    }
    
    int parent[V];
    int key[V];
    vector<bool> mstset(V);
    for(int i=0;i<V;i++)
    {
        key[i]=INT_MAX;
        mstset[i]=false;
        parent[i]=20;
    }
    
    int root;
    root= 0;
    parent[root]=-1;
    
    int vertex_must_include[V];
    map<int, int> parent_included_vertex;
    
    for(int m=0;m<V;m++)
        vertex_must_include[m]=false;
    if(!include_edges.empty())
    {
        for(vector<pair<int, int>>::iterator it=include_edges.begin(); it!=include_edges.end();it++)
        {
            u1=(*it).first;
            v1=(*it).second;
            vertex_must_include[u1]=vertex_must_include[v1]=true;
            parent_included_vertex[v1]=u1;
            parent_included_vertex[u1]=100;
        }
    }
    
    key[root]=0;
    parent[root]=-1;
    for(int c=0;c<V;c++)
    {
        int u=find_min_key(key, V, mstset);
        if(u==-1)//disconnected
        {
            return -1;
        }
        mstset[u]=true;
        mat_cycle[parent[u]][u]=new_mat[parent[u]][u];
        no_of_vert++;
        
        for(int v=0;v<V;v++)
        {
            if(new_mat[u][v]>0 && mstset[v]==false && new_mat[u][v]< key[v])
            {
                
                if(vertex_must_include[v] && parent_included_vertex[v]!=100 && parent_included_vertex[v]!=u)
                {
                    int x=parent_included_vertex[v];
                    if(parent[x]!=20)
                        continue;
                }
                //to check if cycle formed or not
                int prev=mat_cycle[u][v];
                mat_cycle[u][v]=new_mat[u][v];
                
                bool cycle=is_cycle(mat_cycle, root, V);
                if(!cycle)
                {
                    parent[v]=u;
                    key[v]=new_mat[u][v];
                }
                mat_cycle[u][v]=prev;
            }
        }
    }
    int tot_cost=0;
    for(int i=1;i<V;i++){
        int x=parent[i];
        tot_cost+=new_mat[x][i];
        current_span.push_back(make_pair(x, i));
    }
    return tot_cost;
}

void create_partitions(graph G)
{
    while(true)
    {
        int cost_curr_partition;
        int cost_=INT_MAX;
        part P;
        vector<part>::iterator iter;
        for(vector<part>::iterator it=partitions.begin();it!=partitions.end();it++)
        {
            int c=(*it).cost_st;
            if(c<cost_)//to get the st with min cost
            {
                cost_=c;
                iter=it;
            }
        }
        P.spanning=(*iter).spanning;
        P.exc_ed=(*iter).exc_ed;
        P.inc_ed=(*iter).inc_ed;
        P.cost_st=(*iter).cost_st;
        partitions.erase(iter);
        
        vector<pair<int, int>> stree=P.spanning;
        //we print the spanning tree here
        vector<pair<int, int>>::iterator it1;
        vector<pair<int, int>>::iterator it2;
        vector<pair<int, int>>::iterator it_test;
        ans_vector.push_back(make_pair(cost_, stree));
        //now we create partitions on the spanning tree obtained in P
        vector<pair<int, int>> included_edges;
        vector<pair<int, int>> excluded_edges;
        included_edges=P.inc_ed;
        
        pair<int, int> ex_edge;//the new edge to be excluded in every partition
        int j;
        for(j=0;j<30;j++)
        {
            if(included_edges.empty())
                break;
            if(stree[j].first!=included_edges[j].first && stree[j].second!=included_edges[j].second)
            {
                break;
            }
        }
        it2= stree.begin()+ j;
        int u1,v1;
        for(it1=it2; it1!=stree.end(); it1++)
        {
            cout<<"Next Partition: ";
            part new_p;
            u1=(*it1).first;
            v1=(*it1).second;
            ex_edge.first=u1;
            ex_edge.second=v1;
            excluded_edges=P.exc_ed;
            excluded_edges.push_back(ex_edge);
            cout<<"Excluded edges: ";
            for(it_test=excluded_edges.begin();it_test!=excluded_edges.end();it_test++)
                cout<<(*it_test).first<<"-->"<<(*it_test).second<<",";
            cout<<endl;
            cout<<"Included edges: ";
            for(it_test=included_edges.begin();it_test!=included_edges.end();it_test++)
                cout<<(*it_test).first<<"-->"<<(*it_test).second<<",";
            cout<<endl;
            current_span.clear();
            cost_curr_partition=Prim_ST(G, included_edges, excluded_edges);
            if(cost_curr_partition<=0)
                cout<<"DISCONNECTED tree from this partition\n";
            else
            {
                new_p.cost_st=cost_curr_partition;
                new_p.spanning=current_span;
                new_p.inc_ed=included_edges;
                new_p.exc_ed=excluded_edges;
                partitions.push_back(new_p);
                if(cost_curr_partition<min_cost_till_now)
                    min_cost_till_now=cost_curr_partition;
                cout<<"Spanning tree found\n";
            }
            included_edges.push_back(ex_edge);
        }
        //now we have finished craeting partitions from a particular spanning tree in partitions
        if(partitions.empty()){
            cout<<"no partition left\n";
            return;
        }
    }
}

void print_partitions()
{
    cout<<"SPANNING TREES IN ORDER OF INCREASING COST\n";
    for(auto elem: ans_vector)
    {
        for(auto i: elem.second)
        {
            cout<<i.first<<"-->"<<i.second<<",";
        }
        cout<<endl;
        cout<<elem.first<<endl;
    }
}

int main(int argc, const char * argv[]) {
    
    int u1,v1,wt1,vertex;
    char ch;
    cout<<"Please create graph\n";
    cout<<"Enter number of vertices in graph: ";
    cin>>vertex;
    graph G;
    G.Vertex=vertex;
    cout<<"Please note-the numbering of vertices starts from 0 (not 1)\n";
    cout<<"Enter edges with weight>0\n";
    cout<<"Enter edges into graph in the form (source vertex, destination vertex, weight of edge)\n";
    do{
        cin>>u1>>v1>>wt1;
        G.add_edge(u1, v1, wt1);
        if(wt1<=0){
            cout<<"invalid edge!\n";
            return 1;
        }
        cout<<"add another edge?(y/n): ";
        cin>>ch;
    }while(ch=='y');
    //graph has been made
    
    int choice;
    cout<<"Enter choice:\n1.print graph\n2.print all spanning trees of graph in increasing order of cost\n";
    cin>>choice;
    switch(choice){
        case 1:
            G.print();
            break;
        case 2:
            int cost=0;
            cost=Prim_MST(G.adj_mat, vertex);//vector of MST edges
            if(cost<=0)
            {
                cout<<"DISCONNECTED GRAPH, MINIMUM SPANNING TREE CAN'T BE FOUND\n";
                return 0;
            }
            vector<pair<int, int>> incl;
            vector<pair<int, int>> excl;
            //append the MST of the graph to the partitions data structure
            part p;
            incl.clear();
            excl.clear();
            p.exc_ed=excl;
            p.inc_ed=incl;
            p.spanning=current_span;
            p.cost_st=cost;
            partitions.push_back(p);
            min_cost_till_now=cost;
            create_partitions(G);
            print_partitions();
    }
    return 0;
}










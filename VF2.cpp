#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <assert.h>
#include <ctime>

#include <algorithm>
#include <iterator>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;

typedef int VIndex;
typedef int EIndex;
typedef int VLabel;
const VIndex NULL_VIndex = -1;
const EIndex NULL_EIndex = -1;
const set<VIndex> NULL_VERTEX_SET = {};

struct Edge {
  int u, v, label, next, prev;
  Edge(int u, int v, int l, int n, int p): u(u), v(v), label(l), next(n), prev(p) {}
};

/*
* Graph structure
*
* Attributes
* ----------
* vertex_count: int, number of vertices
* edge_count: int, number of edges
* vertex: vector, length = `vertex_count`, label of each vertex
* edge: vector, length = `edge_count`, edges of graph
* head_edge: vector, length = `vertex_count`, ead of linked list
* pred: vector, length = `vertex_count`, predecessors of each vertex
* succ: vector, length = `vertex_count`, successors of each vertex
*
* Methods
* -------
* addVertex: add a vertex whose label is `label`
* addEdge: add an edge from `u` to 'v', and its label is `label`
* initial: initialize a graph
* printGraphInfo: print graph structure
*/
struct Graph {
  int edge_count, vertex_count;
  vector<VLabel> vertex;
  vector<EIndex> head_edge;
  vector<EIndex> rev_head_edge;
  vector<Edge> edge;
  vector<set<VIndex>> pred;
  vector<set<VIndex>> succ;

  void addVertex(int label) {
    vertex.push_back(label);
    head_edge.push_back(NULL_EIndex);
    rev_head_edge.push_back(NULL_EIndex);
    pred.push_back(NULL_VERTEX_SET);
    succ.push_back(NULL_VERTEX_SET);
    vertex_count++;
  }

  void addEdge(int u, int v, int label) {
    edge.push_back(Edge(u, v, label, head_edge[u], rev_head_edge[v]));
    head_edge[u] = edge_count;
    rev_head_edge[v] = edge_count++;
    pred[v].insert(u);
    succ[u].insert(v);
  }

  void initial() {
    vertex_count = edge_count = 0;
    vertex.clear();
    edge.clear();
    head_edge.clear();
    rev_head_edge.clear();
    pred.clear();
    succ.clear();
  }

  void printGraphInfo() const {
    printf("vertex count: %d\n", vertex_count);
    printf("vertex label:\n");
    for (auto v: vertex) printf("%d ", v);
    puts("");
    printf("vertex predecessors:\n");
    int cnt = 0;
    for (auto nodes: pred) {
      printf("No.%d:", cnt++);
      for (auto v: nodes) {
        printf(" %d", v);
      }
      puts("");
    }
    printf("edge count: %d\n", edge_count);
    puts("");
  }
};
vector<Graph> database, query;

void readGraph(vector<Graph> &G, int total) {
  Graph new_graph;
  new_graph.initial();
  char str[10000];
  while (gets(str)) {
    if (strlen(str) == 0) continue;
    stringstream stream;
    if (str[0] == 't') {
      int gid;
      stream << str + 4;
      stream >> gid;
      --total;
      if (gid == 0) continue;
      G.push_back(new_graph);
      if (total == 0) break;
      new_graph.initial();
    } else if (str[0] == 'v') {
      int vid, vlabel;
      stream << str + 2;
      stream >> vid >> vlabel;
      new_graph.addVertex(vlabel);
    } else if (str[0] == 'e') {
      int uid, vid, elabel;
      stream << str + 2;
      stream >> uid >> vid >> elabel;
      new_graph.addEdge(uid, vid, elabel);
    }
  }
  printf("Total size: %d\n", G.size());
}

/*
* Possible state
*
* Attributes
* ----------
* vertex_count: int, the number of vertexes in query graph
* subisomorphism: bool, isomorphism or subgraph isomorphism,
*                 different form of feasibility rules
* in_1, in_2: set, the set of nodes, not yet in the partial mapping, that are
*             the origin of edges ending into G1(s) and G2(s)
* out_1, out_2: set, the set of nodes, not yet in the partial mapping, that are
*             the destination of edges starting from G1(s) and G2(s)
* M1, M2: set, the set of nodes in G1(s) and G2(s)
* core_1, core_2: vector, length=vertex_count(G1 or G2), core_1[u] contains the
*                 index of the node paired with u, if u is in M1(s),
*                 or NULL_VIndex otherwise
*
* Methods
* -------
* genCandiPairSet: computation of the candidate pairs set P(s)
* addNewPair: add a mapping pair (n, m) to current state and update attributes
* checkPredRule, checkSuccRule: check consistency of the partial solution M(s')
*     obtained by adding the considered candidate pair(n, m) to current state
* checkInRule, checkOutRule: pruning the search tree, perform a 1-look-ahead in
*     the searching process
* checkNewRule: pruning the search tree, a 2-look-ahead
* set_intersection_size: int, return the size of intersection of two sets
* genComplementary: set, return the complementary set of M1(s)(or M2(s)) and
*     T1(s)(or T2(s))
* checkSynRules: check all synatic feasibility rules
* checkSemRules: check nodes attributes and edge attributes
*/
struct State {
  int vertex_count;
  bool subisomorphism;
  set<VIndex> in_1, in_2, out_1, out_2;
  set<VIndex> M1, M2;
  vector<VIndex> core_1, core_2;

  State(int _count, bool sub) {
    vertex_count = _count;
    subisomorphism = sub;
    core_1.resize(_count);
    fill(core_1.begin(), core_1.end(), NULL_VIndex);
    core_2.resize(_count);
    fill(core_2.begin(), core_2.end(), NULL_VIndex);
    in_1.clear(), in_2.clear();
    out_1.clear(), out_2.clear();
    M1.clear(), M2.clear();
  }

  vector<pair<VIndex, VIndex>> genCandiPairSet() {
    vector<pair<VIndex, VIndex>> P;
    if (out_1.size() && out_2.size()) {
      VIndex max_vid2 = -1;
      for (auto vid2: out_2) max_vid2 = max(max_vid2, vid2);
      for (auto vid1: out_1) {
        P.push_back(make_pair(vid1, max_vid2));
      }
    } else if (in_1.size() && in_2.size()) {
      VIndex max_vid2 = -1;
      for (auto vid2: in_2) max_vid2 = max(max_vid2, vid2);
      for (auto vid1: in_1) {
        P.push_back(make_pair(vid1, max_vid2));
      }
    } else {
      VIndex max_vid2;
      for (max_vid2 = vertex_count - 1; max_vid2 >= 0 && core_2[max_vid2] !=
                                        NULL_VIndex; max_vid2--) {}
      for (auto vid = 0; vid < vertex_count; vid++) {
        if (core_1[vid] == NULL_VIndex) {
          P.push_back(make_pair(vid, max_vid2));
        }
      }
    }
    /*
    puts("Candidate pair set");
    for (auto p: P) {
      printf("%d %d\n", p.first, p.second);
    }
    */
    return P;
  }

  void addNewPair(VIndex n, VIndex m, const set<VIndex> &pred1, const set<VIndex> &pred2,
                  const set<VIndex> &succ1, const set<VIndex> &succ2) {
    M1.insert(n);
    M2.insert(m);
    core_1[n] = m;
    core_2[m] = n;
    for (auto u: pred1) if (core_1[u] == NULL_VIndex) in_1.insert(u);
    for (auto u: pred2) if (core_2[u] == NULL_VIndex) in_2.insert(u);
    for (auto u: succ1) if (core_1[u] == NULL_VIndex) out_1.insert(u);
    for (auto u: succ2) if (core_2[u] == NULL_VIndex) out_2.insert(u);
    if (in_1.find(n) != in_1.end()) in_1.erase(n);
    if (in_2.find(m) != in_2.end()) in_2.erase(m);
    if (out_1.find(n) != out_1.end()) out_1.erase(n);
    if (out_2.find(m) != out_2.end()) out_2.erase(m);
  }

  bool checkPredRule(const Graph &G1, const Graph &G2, VIndex n, VIndex m) {
    for (EIndex eid = G1.head_edge[n]; eid != NULL_EIndex; eid = G1.edge[eid].next) {
      VIndex vid = G1.edge[eid].v;
      VIndex map_vid = core_1[G1.edge[eid].v];
      if (map_vid == NULL_VIndex) continue;
      int label = G1.edge[eid].label;
      // wehter there is an edge m -> map_vid has the same label as n -> vid
      bool flag = 0;
      for (EIndex eid2 = G2.head_edge[m]; eid2 != NULL_EIndex; eid2 = G2.edge[eid2].next) {
        if (G2.edge[eid2].v == map_vid && G2.edge[eid2].label == label) {
          flag = 1;
          break;
        }
      }
      if (!flag) return false;
    }
    set<VIndex> new_pred;
    set_intersection(M2.begin(), M2.end(), G2.pred[m].begin(), G2.pred[m].end(),
                    inserter(new_pred, new_pred.begin()));
    for (auto v2: new_pred) {
      VIndex v1 = core_2[v2];
      assert(v1 != NULL_VIndex);
      if (G1.pred[n].find(v1) == G1.pred[n].end()) return false;
    }
    return true;
  }

  bool checkSuccRule(const Graph &G1, const Graph &G2, VIndex n, VIndex m) {
    for (EIndex eid = G1.rev_head_edge[n]; eid != NULL_EIndex; eid = G1.edge[eid].prev) {
      VIndex vid = G1.edge[eid].u;
      VIndex map_vid = core_1[G1.edge[eid].u];
      if (map_vid == NULL_VIndex) continue;
      int label = G1.edge[eid].label;
      // wehter there is an edge map_vid -> m has the same label as vid -> n
      bool flag = 0;
      for (EIndex eid2 = G2.rev_head_edge[m]; eid2 != NULL_EIndex; eid2 = G2.edge[eid2].prev) {
        if (G2.edge[eid2].u == map_vid && G2.edge[eid2].label == label) {
          flag = 1;
          break;
        }
      }
      if (!flag) return false;
    }
    set<VIndex> new_succ;
    set_intersection(M2.begin(), M2.end(), G2.succ[m].begin(), G2.succ[m].end(),
                    inserter(new_succ, new_succ.begin()));
    for (auto v2: new_succ) {
      VIndex v1 = core_2[v2];
      assert(v1 != NULL_VIndex);
      if (G1.succ[n].find(v1) == G1.succ[n].end()) return false;
    }
    return true;
  }

  int set_intersection_size(const set<VIndex> &a, const set<VIndex> &b) {
    return count_if(a.begin(), a.end(), [&](int k) { return b.find(k) != b.end(); });
  }

  bool checkInRule(const Graph &G1, const Graph &G2, VIndex n, VIndex m) {
    int card_succ_1 = set_intersection_size(in_1, G1.succ[n]);
    int card_succ_2 = set_intersection_size(in_2, G2.succ[m]);
    if (!subisomorphism && card_succ_1 != card_succ_2) return false;
    if (subisomorphism && card_succ_1 > card_succ_2) return false;
    int card_pred_1 = set_intersection_size(in_1, G1.pred[n]);
    int card_pred_2 = set_intersection_size(in_2, G2.pred[m]);
    if (subisomorphism && card_pred_1 != card_pred_2) return false;
    if (subisomorphism && card_pred_1 > card_pred_2) return false;
    return true;
  }

  bool checkOutRule(const Graph &G1, const Graph &G2, VIndex n, VIndex m) {
    int card_succ_1 = set_intersection_size(out_1, G1.succ[n]);
    int card_succ_2 = set_intersection_size(out_2, G2.succ[m]);
    if (!subisomorphism && card_succ_1 != card_succ_2) return false;
    if (subisomorphism && card_succ_1 > card_succ_2) return false;
    int card_pred_1 = set_intersection_size(out_1, G1.pred[n]);
    int card_pred_2 = set_intersection_size(out_2, G2.pred[m]);
    if (!subisomorphism && card_pred_1 != card_pred_2) return false;
    if (subisomorphism && card_pred_1 > card_pred_2) return false;
    return true;
  }

  set<VIndex> genComplementary(int count, const vector<VIndex> &core,
                              const set<VIndex> &in, const set<VIndex> &out){
    set<VIndex> res;
    for (VIndex vid = 0; vid < count; vid++) {
      if (core[vid] == NULL_VIndex && in.find(vid) == in.end() && out.find(vid) == out.end()) {
        res.insert(vid);
      }
    }
    return res;
  }

  bool checkNewRule(const Graph &G1, const Graph &G2, VIndex n, VIndex m) {
    set<VIndex> _N1 = genComplementary(G1.vertex_count, core_1, in_1, out_1);
    set<VIndex> _N2 = genComplementary(G2.vertex_count, core_2, in_2, out_2);
    int card_pred_1 = set_intersection_size(G1.pred[n], _N1);
    int card_pred_2 = set_intersection_size(G2.pred[m], _N2);
    if (!subisomorphism && card_pred_1 != card_pred_2) return false;
    if (subisomorphism && card_pred_1 > card_pred_2) return false;
    int card_succ_1 = set_intersection_size(G1.succ[n], _N1);
    int card_succ_2 = set_intersection_size(G2.succ[m], _N2);
    if (!subisomorphism && card_succ_1 != card_succ_2) return false;
    if (subisomorphism && card_succ_1 > card_succ_2) return false;
    return true;
  }

  bool checkSynRules(const Graph &G1, const Graph &G2, VIndex n, VIndex m) {
    return checkPredRule(G1, G2, n, m) && checkSuccRule(G1, G2, n, m) &&
           checkInRule(G1, G2, n, m) && checkOutRule(G1, G2, n, m) &&
           checkNewRule(G1, G2, n, m);
  }

  bool checkSemRules(const Graph &G1, const Graph &G2, VIndex n, VIndex m) {
    // node attributes
    if (G1.vertex[n] != G2.vertex[m]) return false;
    // branch attributes
    // move it to checkSuccRule and checkPredRule
    return true;
  }

  void printMapping() {
    printf("%s mapping relationship found:\n", subisomorphism?
          "Subgraph isomorphism": "Isomorphism");
    for (auto i = 0; i < vertex_count; i++) {
      printf("%d %d\n", i, core_1[i]);
    }
  }
};

bool solve(const Graph &G1, const Graph &G2, State &state) {
    // If M(s) covers all the nodes of G2 then output M(s)
    if (state.M1.size() == state.vertex_count) {
      // state.printMapping();
      return true;
    }
    // Compute the set P(s) of the pairs candidate for inclusion in M(s)
    vector<pair<VIndex, VIndex>> P = state.genCandiPairSet();
    // For each p in P(s)
    //   If the feasibility rules succeed for the inclusion of p in M(s) then
    //   Compute the state s' obtained by adding p to M(s)
    //   Call solve(s')
    for (auto p: P) {
      VIndex n = p.first;
      VIndex m = p.second;
      if (state.checkSemRules(G1, G2, n, m) && state.checkSynRules(G1, G2, n, m)) {
        State new_state = state;
        new_state.addNewPair(n, m, G1.pred[n], G2.pred[m], G1.succ[n], G2.succ[m]);
        if (solve(G1, G2, new_state)) return true;
      }
    }
    return false;
}

bool isomorphism(const Graph &G1, const Graph &G2) {
  if (G1.vertex_count != G2.vertex_count) return false;
  if (G1.edge_count != G2.edge_count) return false;
  State state(G1.vertex_count, 0);
  return solve(G1, G2, state);
}

bool subisomorphism(const Graph &G1, const Graph &G2) {
  if (G1.vertex_count > G2.vertex_count) return false;
  if (G1.edge_count > G2.edge_count) return false;
  State state(G1.vertex_count, 1);
  return solve(G1, G2, state);
}

int main() {
  // freopen("graphDB/smalldb.data", "r", stdin);
  freopen("graphDB/mygraphdb.data", "r", stdin);
  readGraph(database, 10000);
  string filename[] = {"graphDB/Q24.my", "graphDB/Q20.my", "graphDB/Q16.my",
  "graphDB/Q12.my", "graphDB/Q8.my", "graphDB/Q4.my"};
  // string filename[] = {"graphDB/smallQ.my"};
  for (auto s: filename) {
    query.clear();
    freopen(s.c_str(), "r", stdin);
    readGraph(query, 1000);
    time_t start_time = 0, end_time = 0;

    time(&start_time);
    for (auto G1: query) {
      for (auto G2: database) {
        isomorphism(G1, G2);
      }
    }
    time(&end_time);
    printf("cost %ld seconds\n", end_time - start_time);
/*
    time(&start_time);
    int gcnt = 0, cnt = 0;
    for (auto G1: query) {
      for (auto G2: database) {
        cnt += subisomorphism(G1, G2);
      }
      gcnt++;
      if (gcnt % 10 == 0) {
        time(&end_time);
        printf("cost %ld seconds\n", end_time - start_time);
      }
    }
    printf("%d\n", cnt);
*/
  }
  return 0;
}

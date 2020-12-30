#include <bitset>
#include <cstring>
#include <cstdlib>
#include <iostream>

using namespace std;

const int MaxV = 800;
const int MaxE = 300000;

template <int MaxSize> class Set {
private:
  int *stack;
  int *index;
  int ssize{};

public:
  Set() {
    stack = new int[MaxSize];
    index = new int[MaxSize];
    clear();
  }

  ~Set() {
    delete[] stack;
    delete[] index;
  }

  int size() const { return ssize; }

  void clear() {
    memset(index, -1, sizeof(int) * MaxSize);
    ssize = 0;
  }

  const int *begin() const { return stack; }

  const int *end() const { return stack + ssize; }

  void insert(int x) {
#ifndef ONLINE_JUDGE
    if (index[x] != -1)
      throw std::runtime_error("Set Error at function insert");
#endif
    stack[index[x] = ssize++] = x;
  }

  void remove(int x) {
#ifndef ONLINE_JUDGE
    if (index[x] == -1)
      throw std::runtime_error("Set Error at function remove");
#endif
    index[stack[index[x]] = stack[--ssize]] = index[x];
    index[x] = -1;
  }
};

class Edge {
public:
  int v1;
  int v2;
  int weight;
};

class Vertex {
public:
  int *adj_v;
  int *adj_e;
  long long time_stamp{};
  int adj_count{};
  int score{};
  bool available{};

  Vertex() {
    adj_v = new int[MaxV];
    adj_e = new int[MaxV];
  }

  ~Vertex() {
    delete[] adj_v;
    delete[] adj_e;
  }

  int adjancet(int e, int v) {
    adj_v[adj_count] = v;
    adj_e[adj_count] = e;
    return adj_count++;
  }

  bool operator>(const Vertex &t) const {
    return score > t.score || (score == t.score && time_stamp < t.time_stamp);
  }
};

int v_num; // |V|: 1...v
int e_num; // |E|: 0...e-1
Edge edges[MaxE];
Vertex vertices[MaxV];
Set<MaxE> uncovered_edges;
Set<MaxV> candidates;
bitset<MaxV> current;
bitset<MaxV> solution;
long long sum_weight;
int just_insert;

int max_steps;
int threshold;
double scale = 0.3;

void insert(int v) {
  current.set(v);
  candidates.insert(v);
  vertices[v].score = -vertices[v].score;
  const int edge_count = vertices[v].adj_count;
  for (int i = 0; i < edge_count; ++i) {
    const int e = vertices[v].adj_e[i];
    const int n = vertices[v].adj_v[i];
    if (!current[n]) {
      vertices[n].score -= edges[e].weight;
      vertices[n].available = true;
      uncovered_edges.remove(e);
    } else {
      vertices[n].score += edges[e].weight;
    }
  }
}

void remove(int v) {
  current.reset(v);
  candidates.remove(v);
  vertices[v].score = -vertices[v].score;
  vertices[v].available = false;
  const int edge_count = vertices[v].adj_count;
  for (int i = 0; i < edge_count; ++i) {
    const int e = vertices[v].adj_e[i];
    const int n = vertices[v].adj_v[i];
    if (!current[n]) {
      vertices[n].score += edges[e].weight;
      vertices[n].available = true;
      uncovered_edges.insert(e);
    } else {
      vertices[n].score -= edges[e].weight;
    }
  }
}

void forget_weights() {
  for (int v = 1; v <= v_num; v++)
    vertices[v].score = 0;
  sum_weight = 0;
  for (int e = 0; e < e_num; e++) {
    edges[e].weight = (int)(edges[e].weight * scale);
    sum_weight += edges[e].weight;
    if (!(current[edges[e].v1] || current[edges[e].v2])) {
      vertices[edges[e].v1].score += edges[e].weight;
      vertices[edges[e].v2].score += edges[e].weight;
    } else if (current[edges[e].v1] && !current[edges[e].v2]) {
      vertices[edges[e].v1].score -= edges[e].weight;
    } else if (!current[edges[e].v1] && current[edges[e].v2]) {
      vertices[edges[e].v2].score -= edges[e].weight;
    }
  }
}

void update_weight() {
  const int *begin = uncovered_edges.begin();
  const int *end = uncovered_edges.end();
  for (const int *it = begin; it != end; ++it) {
    const int &e = *it;
    edges[e].weight += 1;
    vertices[edges[e].v1].score += 1;
    vertices[edges[e].v2].score += 1;
  }
  sum_weight += uncovered_edges.size();
  long long avg_weight = sum_weight / e_num;
  if (avg_weight >= threshold)
    forget_weights();
}

int select_v_to_remove() {
  const int *begin = candidates.begin();
  const int *end = candidates.end();
  int r = *begin;
  for (const int *it = begin; it != end; ++it) {
    const int &v = *it;
    if (v != just_insert && vertices[v] > vertices[r])
      r = v;
  }
  return r;
}

int select_v_to_insert() {
  const int e = uncovered_edges.begin()[rand() % uncovered_edges.size()];
  const int &v1 = edges[e].v1;
  const int &v2 = edges[e].v2;
  if (!vertices[v1].available)
    return v2;
  else if (!vertices[v2].available)
    return v1;
  else
    return vertices[v1] > vertices[v2] ? v1 : v2;
}

void initialize() {
  current.reset();
  candidates.clear();
  uncovered_edges.clear();
  for (int v = 1; v <= v_num; v++) {
    vertices[v].score = 0;
    vertices[v].time_stamp = 0;
    vertices[v].available = true;
  }
  for (int e = 0; e < e_num; e++) {
    edges[e].weight = 1;
    vertices[edges[e].v1].score += 1;
    vertices[edges[e].v2].score += 1;
    uncovered_edges.insert(e);
  }
  static int buffer[MaxV];
  while (uncovered_edges.size()) {
    int count = 0, score = 0;
    for (int v = 1; v <= v_num; ++v)
      if (!current[v]) {
        if (vertices[v].score > score) {
          score = vertices[v].score;
          count = 0;
        }
        if (vertices[v].score == score)
          buffer[count++] = v;
      }
    insert(buffer[rand() % count]);
  }
  solution = current;
  just_insert = 0;
}

void algorithm() {
  for (int steps = 1; steps <= max_steps && current.count(); steps++) {
    if (!uncovered_edges.size()) {
      solution = current;
      int v = 0, score = -1000000000;
      for (int i = 1; i <= v_num; ++i)
        if (current[i] && vertices[i].score > score)
          score = vertices[v = i].score;
      remove(v);
      continue;
    }
    const int v_remove = select_v_to_remove();
    remove(v_remove);
    const int v_insert = select_v_to_insert();
    insert(v_insert);
    vertices[v_remove].time_stamp = steps;
    vertices[v_insert].time_stamp = steps;
    just_insert = v_insert;
    update_weight();
  }
}

bool openjudge_input() {
  static bool G[MaxV][MaxV];
  int n, m;
  if (cin >> n >> m) {
    memset(G, 0, sizeof(G));
    for (int i = 0, u, v; i < m; ++i) {
      cin >> u >> v;
      G[u][v] = true;
      G[v][u] = true;
    }
    v_num = n;
    e_num = 0;
    for (int i = 1; i <= n; i++)
      vertices[i].adj_count = 0;
    for (int i = 1; i <= n; ++i)
      for (int j = 1; j < i; ++j)
        if (!G[i][j]) {
          edges[e_num].v1 = i;
          edges[e_num].v2 = j;
          vertices[i].adjancet(e_num, j);
          vertices[j].adjancet(e_num, i);
          e_num++;
        }
    return true;
  }
  return false;
}

void openjudge_output() {
  cout << v_num - solution.count() << endl;
  for (int i = 1; i <= v_num; i++)
    if (!solution[i])
      cout << i << " ";
  cout << endl;
}

struct Options {
  int numV;
  int seed;
  int steps;
  double scale;
  double threshold;

  Options(int _numV, int _seed, int _steps, double _scale, double _threshold)
      : numV(_numV), seed(_seed), steps(_steps), scale(_scale),
        threshold(_threshold) {}
};

// #define EXPERIMENTAL

const Options options[] = {
#ifdef EXPERIMENTAL

#else
    Options(20, 7, 10, 0.3, 0.5),          // 9
    Options(30, 7, 20, 0.3, 0.5),          // 13
    Options(40, 9, 20, 0.3, 0.5),          // 14
    Options(60, 7, 20, 0.3, 0.5),          // 19
    Options(80, 7, 30, 0.3, 0.5),          // 22
    Options(100, 20201231, 300, 0.3, 0.5), // 24
    Options(200, 7, 10000, 0.3, 0.5),      // 29
    Options(300, 7, 30000, 0.3, 0.5),      // 33
    Options(400, 7, 30000, 0.3, 0.5),      // 30
    Options(500, 7, 50000, 0.3, 0.5),      // 35
    Options(750, 7, 350000, 0.3, 0.5),     // 40
#endif
    Options(-1, 7, 0, 0.3, 0.5)};

void set_hyperparameters() {
  const Options *begin = options;
  const Options *end = begin + sizeof(options) / sizeof(Options);
#ifndef ONLINE_JUDGE
  cerr << end - begin << " options in table" << endl;
#endif
  for (const Options *it = begin; it != end; ++it) {
    const Options &opt = *it;
    if (opt.numV == -1 || opt.numV == v_num) {
      srand(opt.seed);
      max_steps = opt.steps;
      scale = opt.scale;
      threshold = (int)(opt.threshold * v_num);
      break;
    }
  }
}

int main() {
#ifdef ONLINE_JUDGE
  ios::sync_with_stdio(false);
  cin.tie(nullptr);
  cout.tie(nullptr);
  cerr.tie(nullptr);
#endif
  while (openjudge_input()) {
    set_hyperparameters();
    if (max_steps > 0) {
      initialize();
      algorithm();
      openjudge_output();
    } else {
      cout << 0 << endl;
    }
  }
  return 0;
}
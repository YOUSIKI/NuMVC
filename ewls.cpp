//#define DEBUG

#include <list>
#include <set>
#include <vector>
#include <stack>
#include <ctime>
#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <iostream>
#include <algorithm>

using namespace std;


#define rep(i, l, r) for(int i=(l);(i)<=(r);++(i))

#ifdef DEBUG
#define debug(...) fprintf(stderr, __VA_ARGS__)
#else
#define debug(...)
#endif

typedef std::list<int>::iterator P;
typedef std::pair<int, int> pii;
#define mp std::make_pair
using std::stack;
using std::vector;
using std::sort;
using std::list;

const int N = 4010;
const int M = 2200010;

// Hyperparameters
const int SEED = 20201225;
const int DELTA = 1;
const int MAX_STEP = 100000;

struct E {
    int to, next, id;
} e[M];
int head[N], tote;

void adde(int u, int v, int id) {
    e[++tote] = (E) {v, head[u], id};
    head[u] = tote;
}

int randint(int n) { return rand() % n; }

int iter;
int ans_id;
char buf[256];
int n, m;
int w[N][N], eid[N][N];
int u[M], v[M], c[M], checked[M], lastvis[M];
int dscore[N];
int in_c[N], size_c, best_size_c, ans_c[N];
int max_cover_w[N];
P list_P[M];
int cover_edge;
int begin_time;
int conf_change[N];

list<int> L;

void ins_c(int u) {
    if (in_c[u]) debug("[ERROR] inserting existing vertice\n");
    dscore[u] = 0;
    for (int p = head[u]; p; p = e[p].next)
        if (!in_c[e[p].to]) {
            conf_change[e[p].to] = 1;
            ++cover_edge;
            dscore[e[p].to] -= c[e[p].id];
            dscore[u] -= c[e[p].id];
            L.erase(list_P[e[p].id]);
            list_P[e[p].id] = L.end();
        } else dscore[e[p].to] += c[e[p].id];
    //C.insert(u);
    in_c[u] = 1;
    ++size_c;
}

void rm_c(int u) {
    if (!in_c[u]) debug("[ERROR] deleting not existing vertice\n");
    conf_change[u] = 0;
    dscore[u] = 0;
    for (int p = head[u]; p; p = e[p].next)
        if (!in_c[e[p].to]) {
            --cover_edge;
            conf_change[e[p].to] = 1;
            dscore[e[p].to] += c[e[p].id];
            dscore[u] += c[e[p].id];
            lastvis[e[p].id] = iter;
            list_P[e[p].id] = L.insert(L.end(), e[p].id);
        } else dscore[e[p].to] -= c[e[p].id];
    //C.erase(u);
    in_c[u] = 0;
    --size_c;
}

int score(int u, int v) {
    if (eid[u][v]) return dscore[u] + dscore[v] + c[eid[u][v]];
    else return dscore[u] + dscore[v];
}

int covered(int edge) {
    return in_c[u[edge]] + in_c[v[edge]];
}

void calc_dscore() { // O(m)
    rep(i, 1, n) {
        int t = 0;
        for (int p = head[i]; p; p = e[p].next) {
            if (!in_c[e[p].to]) t += c[e[p].id];
        }
        dscore[i] = in_c[i] ? -t : t;
    }
}

void remove_vertices(int cnt) {
    rep(_, 1, cnt) {
        int q = -1;
        rep(i, 1, n) if (in_c[i] && (q == -1 || dscore[q] < dscore[i])) q = i;
        rm_c(q);
    }
}

int random_from_c() {
    if (!size_c) return -1;
    int cnt = randint(size_c);
    rep(i, 1, n) if (in_c[i] && !(cnt--)) return i;
    return -1;
}

int endpoint_l[N];

int random_from_l() { // O(n)
    //TODO: optimize
    int t = 0;
    rep(i, 1, n) endpoint_l[i] = 0;
    for (P it = L.begin(); it != L.end(); ++it)
        endpoint_l[u[*it]] = endpoint_l[v[*it]] = 1;
    rep(i, 1, n) t += endpoint_l[i];
    if (!t) return -1;
    int cnt = randint(t);
    rep(i, 1, n) if (endpoint_l[i] && !(cnt--)) return i;
    return -1;

}

pii s[M];
int tots, max_c_dscore;

int cmp_age(int x, int y) {
    return lastvis[x] < lastvis[y];
}

pii choose_exchange_u(int v1, int v2) {
//    if (!conf_change[v1] && !conf_change[v2]) return mp(0, 0);
    tots = 0;
    rep(j, 1, n) if (in_c[j]) {
            if (score(j, v1) > 0) s[++tots] = mp(j, v1);
            if (score(j, v2) > 0) s[++tots] = mp(j, v2);
//            if (conf_change[v1] && score(j, v1) > 0) s[++tots] = mp(j, v1);
//            if (conf_change[v2] && score(j, v2) > 0) s[++tots] = mp(j, v2);
        }
    //rep(j,1,n) if (in_c[j]) {
    //	if (conf_change[v1] && score(j,v1)>0) s[++tots]=mp(j,v1);
    //	if (conf_change[v2] && score(j,v2)>0) s[++tots]=mp(j,v2);
    //}
    if (tots) return s[randint(tots)];
    //int mxscore,p=-1;
    //for (int i=1;i<=tots;++i) {
    //	if (p==-1 || score(s[i].first, s[i].second)>mxscore) {
    //		mxscore = score(s[i].first, s[i].second);
    //		p=i;
    //	}
    //}
    //if (p!=-1) return s[p];
    return mp(0, 0);
}

pii choose_exchange_pair() { // O(m)
    // TODO: maintain UL
    //debug("%d*%d\n", C.size(), L.size());
    if (L.empty()) return mp(0, 0);
    max_c_dscore = -1e9;
    //rep(i,1,n) if (in_c[i] && max_c_dscore<dscore[i])
    //max_c_dscore = dscore[i];
    pii t = choose_exchange_u(u[*L.begin()], v[*L.begin()]);
    if (t.first != 0) return t;
    for (P it = L.begin(); it != L.end(); ++it)
        if (!checked[*it]) {
            checked[*it] = 1;
            t = choose_exchange_u(u[*it], v[*it]);
            if (t.first != 0) return t;
        }
    return mp(0, 0);
}

void random_swap() {
    int u = random_from_c();
    int v = random_from_l();
    if (u != -1 && v != -1) {
        rm_c(u);
        ins_c(v);
    }
}

void solve(int Step) {
    rep(i, 1, n) conf_change[i] = 1;
    rep(i, 1, n) max_cover_w[i] = 1;
    rep(i, 1, n) in_c[i] = 0;
    rep(i, 1, m) c[i] = 1;
    rep(i, 1, m) list_P[i] = L.insert(L.end(), i);

    // construct C greedily
    calc_dscore();
    debug("construct C\n");
    while (cover_edge != m) {
        // choose q with max dscore
        // TODO: randomize
        int q = -1;
        rep(i, 1, n) if (!in_c[i] && (q == -1 || dscore[q] < dscore[i])) q = i;
        // add q to C, update dscore
        ins_c(q);
    }
    best_size_c = size_c;
    rep(i, 1, n) ans_c[i] = in_c[i];

    remove_vertices(DELTA);

    for (iter = 1; iter <= Step; ++iter) {
        if (iter % 10000 == 0) {
            debug("iter: %d\n", iter);
        }
        pii t = choose_exchange_pair();
        if (t.first != 0) {
            rm_c(t.first);
            ins_c(t.second);
        } else {
            // update edge
            rep(i, 1, m) {
                checked[i] = 0;
                if (!covered(i)) {
                    ++c[i];
                    conf_change[u[i]] = 1;
                    conf_change[v[i]] = 1;
                    if (!in_c[u[i]]) dscore[v[i]] += in_c[v[i]] ? -1 : 1;
                    if (!in_c[v[i]]) dscore[u[i]] += in_c[u[i]] ? -1 : 1;
                }
                //if (c[i]>max_cover_w[u[i]]) max_cover_w[u[i]]=c[i];
                //if (c[i]>max_cover_w[v[i]]) max_cover_w[v[i]]=c[i];
            }
            // take a random step
            random_swap();
        }

        if (size_c + (m - cover_edge) < best_size_c) {
            stack<int> c_plus;
            static int uncover_edge[N];
            while (m != cover_edge) {
                rep(i, 1, n) if (!in_c[i]) {
                        uncover_edge[i] = 0;
                        for (int p = head[i]; p; p = e[p].next)
                            if (!in_c[e[p].to]) ++uncover_edge[i];
                    }
                // find vertice that covers most uncovered edges
                int q = -1;
                rep(i, 1, n) if (!in_c[i] && (q == -1 || uncover_edge[i] > uncover_edge[q])) q = i;
                c_plus.push(q);
                ins_c(q);
            }
            best_size_c = size_c;
            rep(i, 1, n) ans_c[i] = in_c[i];
            while (!c_plus.empty()) rm_c(c_plus.top()), c_plus.pop();
            remove_vertices(DELTA);
            rep(i, 1, m) checked[i] = 0;
        }
    }
}

void init() {
    tote = 0;
    iter = 0;
    ans_id = 0;
    best_size_c = 0;
    cover_edge = 0;
    size_c = 0;
    rep(i, 1, n) rep(j, 1, n) w[i][j] = eid[i][j] = 0;
    rep(i, 1, n) {
        in_c[i] = 0;
        ans_c[i] = 0;
        dscore[i] = 0;
        head[i] = 0;
    }
    L.clear();
}

void frb_test() {
    srand(SEED);
    init();
    string tmp;
    cin >> tmp >> tmp >> n >> m;
    cerr << "v_num = " << n << endl;
    cerr << "e_num = " << m << endl;
    rep(i, 1, m) {
        cin >> tmp >> u[i] >> v[i];
        adde(u[i], v[i], i);
        adde(v[i], u[i], i);
        w[u[i]][v[i]] = w[v[i]][u[i]] = 1;
        eid[u[i]][v[i]] = eid[v[i]][u[i]] = i;
    }
    time_t start_time = time(0);
    solve(MAX_STEP);
    time_t end_time = time(0);
    cout << best_size_c << endl;
    cout << "used_time: " << end_time - start_time << endl;
}

int main() {
    frb_test();
}

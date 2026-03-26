/**
 * Area- and Topology-Preserving Polygon Simplification
 * Implements the APSC algorithm from Kronenfeld et al. (2020)
 *
 * Key data structures:
 *   - Per-ring doubly-linked circular list (flat vertex pool, O(1) removal)
 *   - Min-heap priority queue with lazy deletion via version counters
 *   - Uniform-grid spatial index for fast intersection queries
 *
 * Build:  make
 * Usage:  ./simplify <input.csv> <target_vertices>
 */
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <queue>
#include <sstream>
#include <string>
#include <vector>

 // ?? Geometry ??????????????????????????????????????????????????????????????????

struct Point { double x, y; };

static inline double cross2(const Point& A, const Point& B, const Point& C) {
    return (B.x - A.x) * (C.y - A.y) - (B.y - A.y) * (C.x - A.x);
}
static inline bool onSeg(const Point& P, const Point& A, const Point& B) {
    return std::min(A.x, B.x) <= P.x && P.x <= std::max(A.x, B.x)
        && std::min(A.y, B.y) <= P.y && P.y <= std::max(A.y, B.y);
}
static bool segInt(const Point& p1, const Point& p2,
    const Point& p3, const Point& p4) {
    auto same = [](const Point& a, const Point& b) {return a.x == b.x && a.y == b.y; };
    if (same(p1, p3) || same(p1, p4) || same(p2, p3) || same(p2, p4)) return false;
    double d1 = cross2(p3, p4, p1), d2 = cross2(p3, p4, p2);
    double d3 = cross2(p1, p2, p3), d4 = cross2(p1, p2, p4);
    if (((d1 > 0 && d2 < 0) || (d1 < 0 && d2>0)) && ((d3 > 0 && d4 < 0) || (d3 < 0 && d4>0))) return true;
    if (d1 == 0.0 && onSeg(p1, p3, p4)) return true;
    if (d2 == 0.0 && onSeg(p2, p3, p4)) return true;
    if (d3 == 0.0 && onSeg(p3, p1, p2)) return true;
    if (d4 == 0.0 && onSeg(p4, p1, p2)) return true;
    return false;
}

// ?? Vertex pool ????????????????????????????????????????????????????????????????

struct Vertex { double x, y; int ring_id, prev, next; bool alive; int version; };
static std::vector<Vertex> V;

// ?? Compute E for collapse A?B?C?D ? A?E?D ???????????????????????????????????
//
// Area constraint: signed_area(A,E,D) = signed_area(A,B,C,D)
// Optimal E (minimum displacement): foot of perpendicular from midpoint(B,C)
// to the constraint line (which has normal direction D-A).
//
// Areal displacement: find crossing P of new path A?E?D with old segment B?C;
// displacement = |tri(B,E,P)| + |tri(P,C,D)|.
// Since area is preserved, both lobes are equal ? displacement = 2|tri(B,E,P)|.
// Fallback if no crossing found: sum of abs triangle areas.

static bool computeCollapse(const Point& A, const Point& B,
    const Point& C, const Point& D,
    Point& E, double& cost) {
    // 2× signed area of quad A,B,C,D (shoelace)
    double S2 = (A.x * B.y - B.x * A.y) + (B.x * C.y - C.x * B.y)
        + (C.x * D.y - D.x * C.y) + (D.x * A.y - A.x * D.y);
    double adx = D.x - A.x, ady = D.y - A.y, ad2 = adx * adx + ady * ady;
    if (ad2 < 1e-20) return false;
    double Mx = (B.x + C.x) * 0.5, My = (B.y + C.y) * 0.5;
    // 2× signed area of triangle A,M,D
    double SM2 = (A.x * My - Mx * A.y) + (Mx * D.y - D.x * My) + (D.x * A.y - A.x * D.y);
    // Shift M perpendicular to AD: normal direction = (-ady, adx)
    // shift t: SM2 + t*(-ad2) = S2  ?  t = (SM2-S2)/ad2
    double t = (SM2 - S2) / ad2;
    E = { Mx + t * (-ady),My + t * adx };

    // Areal displacement via crossing point P of new path with old segment B?C
    auto triAbs = [](const Point& p, const Point& q, const Point& r) {
        return 0.5 * std::abs(cross2(p, q, r)); };
    auto intersectST = [](const Point& p1, const Point& p2,
        const Point& p3, const Point& p4, double& s, double& tv)->bool {
            double dx1 = p2.x - p1.x, dy1 = p2.y - p1.y;
            double dx2 = p4.x - p3.x, dy2 = p4.y - p3.y;
            double dxo = p3.x - p1.x, dyo = p3.y - p1.y;
            double den = dx1 * dy2 - dy1 * dx2;
            if (std::abs(den) < 1e-15) return false;
            s = (dxo * dy2 - dyo * dx2) / den; tv = (dxo * dy1 - dyo * dx1) / den;
            return true;
        };
    const double lo = -1e-9, hi = 1 + 1e-9, in = 1e-9, out = 1 - 1e-9;
    double s, tv; Point P; bool found = false;
    // E?D crosses B?C
    if (!found && intersectST(E, D, B, C, s, tv) && s >= lo && s <= hi && tv >= lo && tv <= hi)
    {
        P = { E.x + s * (D.x - E.x),E.y + s * (D.y - E.y) }; found = true;
    }
    // A?E crosses B?C
    if (!found && intersectST(A, E, B, C, s, tv) && s >= lo && s <= hi && tv >= lo && tv <= hi)
    {
        P = { A.x + s * (E.x - A.x),A.y + s * (E.y - A.y) }; found = true;
    }
    // E?D crosses A?B (interior)
    if (!found && intersectST(E, D, A, B, s, tv) && s > in && s<out && tv>in && tv < out)
    {
        P = { E.x + s * (D.x - E.x),E.y + s * (D.y - E.y) }; found = true;
    }
    // A?E crosses C?D (interior)
    if (!found && intersectST(A, E, C, D, s, tv) && s > in && s<out && tv>in && tv < out)
    {
        P = { A.x + s * (E.x - A.x),A.y + s * (E.y - A.y) }; found = true;
    }

    if (found)
        cost = triAbs(B, E, P) + triAbs(P, C, D);
    else
        cost = triAbs(A, B, E) + triAbs(B, C, E) + triAbs(C, D, E);
    return true;
}

// ?? Candidate ??????????????????????????????????????????????????????????????????

struct Candidate { double cost; int b_idx, b_ver; double ex, ey; };
struct CandCmp { bool operator()(const Candidate& a, const Candidate& b)const { return a.cost > b.cost; } };
static std::priority_queue<Candidate, std::vector<Candidate>, CandCmp> pq;

// ?? Uniform-grid spatial index ?????????????????????????????????????????????????
//
// Edges are stored by their "from" vertex index.
// cellRange: maps a bounding box to a range of grid cells.
// Bug-fix vs naive: use floor division and clamp correctly so boundary edges
// (where lx==hx or coordinate exactly equals cell boundary) don't fall outside.

struct Grid {
    double ox, oy, cell;
    int cols, rows;
    std::vector<std::vector<int>> cells;
    // Per-vertex "seen" generation for deduplication in anyIntersect
    mutable std::vector<int> seen_gen;
    mutable int cur_gen = 0;

    void cellRange(double lx, double hx, double ly, double hy,
        int& c0, int& c1, int& r0, int& r1) const {
        // Use floor + clamp; ensure c0<=c1 and r0<=r1 always
        c0 = std::max(0, (int)std::floor((lx - ox) / cell));
        c1 = std::min(cols - 1, (int)std::floor((hx - ox) / cell));
        r0 = std::max(0, (int)std::floor((ly - oy) / cell));
        r1 = std::min(rows - 1, (int)std::floor((hy - oy) / cell));
        // Clamp c0,r0 to valid range too
        c0 = std::min(c0, cols - 1); r0 = std::min(r0, rows - 1);
    }

    void build(int n_orig) {
        if (V.empty()) return;
        double mnx = 1e300, mny = 1e300, mxx = -1e300, mxy = -1e300;
        for (auto& v : V) if (v.alive) {
            mnx = std::min(mnx, v.x); mny = std::min(mny, v.y);
            mxx = std::max(mxx, v.x); mxy = std::max(mxy, v.y);
        }
        // Expand bbox slightly so boundary vertices don't land on exact cell edge
        double eps = 1e-6;
        mnx -= eps; mny -= eps; mxx += eps; mxy += eps;
        double span = std::max(mxx - mnx, mxy - mny);
        if (span < 1e-12) span = 1.0;
        // Use sqrt(n) for grid side so each cell holds ~1 edge on average.
        // This keeps per-query cell count small even for long segments.
        int side = std::max(1, std::min(3000, (int)std::sqrt((double)n_orig)));
        cols = rows = side; cell = span / side; ox = mnx; oy = mny;
        cells.assign(cols * rows, {});
        seen_gen.assign(V.size() * 2 + 16, 0); // extra room for new vertices
        cur_gen = 0;
        for (int i = 0; i < (int)V.size(); ++i)
            if (V[i].alive) insEdge(i);
    }

    void insEdge(int u) {
        int nv = V[u].next; if (nv < 0 || nv >= (int)V.size()) return;
        double lx = std::min(V[u].x, V[nv].x), hx = std::max(V[u].x, V[nv].x);
        double ly = std::min(V[u].y, V[nv].y), hy = std::max(V[u].y, V[nv].y);
        int c0, c1, r0, r1; cellRange(lx, hx, ly, hy, c0, c1, r0, r1);
        for (int r = r0; r <= r1; ++r) for (int c = c0; c <= c1; ++c)
            cells[r * cols + c].push_back(u);
    }

    void remEdge(int u) {
        int nv = V[u].next; if (nv < 0 || nv >= (int)V.size()) return;
        double lx = std::min(V[u].x, V[nv].x), hx = std::max(V[u].x, V[nv].x);
        double ly = std::min(V[u].y, V[nv].y), hy = std::max(V[u].y, V[nv].y);
        int c0, c1, r0, r1; cellRange(lx, hx, ly, hy, c0, c1, r0, r1);
        for (int r = r0; r <= r1; ++r) for (int c = c0; c <= c1; ++c) {
            auto& cl = cells[r * cols + c];
            for (int i = (int)cl.size() - 1; i >= 0; --i)
                if (cl[i] == u) { cl[i] = cl.back(); cl.pop_back(); break; }
        }
    }

    // Does segment (pa,pb) intersect any live edge, excluding edges incident to skip[0..nskip-1]?
    // Uses a deduplicated scan over touched cells.
    bool anyIntersect(const Point& pa, const Point& pb,
        const int skip[], int nskip) const {
        double lx = std::min(pa.x, pb.x), hx = std::max(pa.x, pb.x);
        double ly = std::min(pa.y, pb.y), hy = std::max(pa.y, pb.y);
        int c0, c1, r0, r1; cellRange(lx, hx, ly, hy, c0, c1, r0, r1);
        ++cur_gen;
        // Grow seen_gen if needed (new vertices added after build)
        if ((int)seen_gen.size() < (int)V.size()) seen_gen.resize(V.size() * 2, 0);
        for (int r = r0; r <= r1; ++r) for (int c = c0; c <= c1; ++c)
            for (int u : cells[r * cols + c]) {
                // Dedup: each edge keyed by 'u' (from-vertex)
                if (u >= (int)seen_gen.size()) continue;
                if (seen_gen[u] == cur_gen) continue;
                seen_gen[u] = cur_gen;
                if (!V[u].alive) continue;
                int nv = V[u].next;
                if (nv < 0 || nv >= (int)V.size() || !V[nv].alive) continue;
                bool sk = false;
                for (int k = 0; k < nskip; ++k) if (u == skip[k] || nv == skip[k]) { sk = true; break; }
                if (sk) continue;
                if (segInt(pa, pb, { V[u].x,V[u].y }, { V[nv].x,V[nv].y })) return true;
            }
        return false;
    }
} grid;

// ?? Push candidate ?????????????????????????????????????????????????????????????

static std::vector<int> ring_size;

static void pushCand(int b) {
    if (b < 0 || b >= (int)V.size() || !V[b].alive) return;
    int a = V[b].prev, c = V[b].next;
    if (c < 0 || !V[c].alive) return;
    int d = V[c].next; if (d < 0) return;
    if (a == c || a == d || b == d) return;
    if (ring_size[V[b].ring_id] < 4) return; // ring must stay >=3 after collapse
    Point A{ V[a].x,V[a].y }, B{ V[b].x,V[b].y }, C{ V[c].x,V[c].y }, D{ V[d].x,V[d].y };
    Point E; double cost;
    if (!computeCollapse(A, B, C, D, E, cost)) return;
    pq.push({ cost,b,V[b].version,E.x,E.y });
}

// ?? Topology check ?????????????????????????????????????????????????????????????

static bool topoOK(int a, int b, int c, int d, const Point& E) {
    Point A{ V[a].x,V[a].y }, D_{ V[d].x,V[d].y };
    int skip[] = { a,b,c,d };
    if (grid.anyIntersect(A, E, skip, 4)) return false;
    if (grid.anyIntersect(E, D_, skip, 4)) return false;
    return true;
}

// ?? Perform collapse ????????????????????????????????????????????????????????????

static void doCollapse(int a, int b, int c, int d, const Point& E) {
    // Remove old edges: A?B (keyed on a), B?C (keyed on b), C?D (keyed on c)
    grid.remEdge(a); grid.remEdge(b); grid.remEdge(c);
    // Kill B and C
    V[b].alive = false; ++V[b].version;
    V[c].alive = false; ++V[c].version;
    // Create new vertex E
    int e = (int)V.size();
    V.push_back({ E.x,E.y,V[a].ring_id,a,d,true,0 });
    // Relink A ? E ? D
    V[a].next = e; ++V[a].version;
    V[d].prev = e; ++V[d].version;
    // Update ring size (net: ?B, ?C, +E = ?1)
    ring_size[V[a].ring_id]--;
    // Add new edges: A?E (keyed on a), E?D (keyed on e)
    grid.insEdge(a); grid.insEdge(e);
    // Re-seed candidates in the neighbourhood
    int pa = V[a].prev; int ppa = (pa >= 0 ? V[pa].prev : -1);
    if (ppa >= 0) pushCand(ppa);
    pushCand(pa); pushCand(a); pushCand(e); pushCand(d);
}

// ?? Signed area of ring starting at 'start' ????????????????????????????????????

static double ringArea(int start) {
    double s = 0.0; int cur = start;
    do { int nv = V[cur].next; s += V[cur].x * V[nv].y - V[nv].x * V[cur].y; cur = nv; } while (cur != start);
    return s * 0.5;
}

// ?? Main ???????????????????????????????????????????????????????????????????????

int main(int argc, char* argv[]) {
    if (argc != 3) { std::cerr << "Usage: " << argv[0] << " <input.csv> <target_vertices>\n"; return 1; }
    const char* fname = argv[1];
    int target = std::atoi(argv[2]);

    // Parse CSV
    std::ifstream f(fname);
    if (!f) { std::cerr << "Cannot open " << fname << "\n"; return 1; }
    struct Row { int rid, vid; double x, y; };
    std::vector<Row> rows; int max_ring = -1;
    std::string line;
    std::getline(f, line); // skip header
    while (std::getline(f, line)) {
        if (line.empty()) continue;
        Row r; char comma;
        std::istringstream ss(line);
        if ((ss >> r.rid >> comma >> r.vid >> comma >> r.x >> comma >> r.y)) {
            rows.push_back(r); if (r.rid > max_ring) max_ring = r.rid;
        }
    }

    // Sort by (ring_id, vertex_id) so rings are contiguous
    std::sort(rows.begin(), rows.end(), [](const Row& a, const Row& b) {
        return a.rid < b.rid || (a.rid == b.rid && a.vid < b.vid); });

    int n_rings = max_ring + 1;
    std::vector<int> ring_head(n_rings, -1);
    std::vector<int> ring_start_v(n_rings, -1); // first V-index per ring
    ring_size.assign(n_rings, 0);

    // Build vertex pool with doubly-linked circular lists
    V.reserve(rows.size() * 2);
    V.resize(rows.size());
    int cur_ring = -1, first = -1, prev_i = -1;
    for (int i = 0; i < (int)rows.size(); ++i) {
        int rid = rows[i].rid;
        V[i] = { rows[i].x,rows[i].y,rid,-1,-1,true,0 };
        if (rid != cur_ring) {
            if (prev_i >= 0 && first >= 0) { V[prev_i].next = first; V[first].prev = prev_i; }
            cur_ring = rid; first = i; prev_i = -1; ring_head[rid] = i; ring_start_v[rid] = i;
        }
        if (prev_i >= 0) { V[prev_i].next = i; V[i].prev = prev_i; }
        ring_size[rid]++; prev_i = i;
    }
    if (prev_i >= 0 && first >= 0) { V[prev_i].next = first; V[first].prev = prev_i; }

    int total_alive = (int)rows.size();

    // Compute input signed area
    double input_area = 0.0;
    for (int r = 0; r < n_rings; ++r) if (ring_head[r] >= 0) input_area += ringArea(ring_head[r]);

    // Early exit
    if (total_alive <= target) {
        printf("ring_id,vertex_id,x,y\n");
        for (int r = 0; r < n_rings; ++r) {
            if (ring_head[r] < 0) continue;
            int cur = ring_head[r], vid = 0;
            do { printf("%d,%d,%.10g,%.10g\n", r, vid++, V[cur].x, V[cur].y); cur = V[cur].next; } while (cur != ring_head[r]);
        }
        printf("Total signed area in input: %.6e\n", input_area);
        printf("Total signed area in output: %.6e\n", input_area);
        printf("Total areal displacement: %.6e\n", 0.0);
        return 0;
    }

    // Build spatial grid and seed heap
    grid.build(total_alive);
    for (int i = 0; i < total_alive; ++i) pushCand(i);

    // APSC main loop
    double disp_accum = 0.0;
    while (total_alive > target && !pq.empty()) {
        auto cand = pq.top(); pq.pop();
        int b = cand.b_idx;
        if (!V[b].alive || V[b].version != cand.b_ver) continue;
        int c = V[b].next; if (!V[c].alive) continue;
        int a = V[b].prev, d = V[c].next;
        if (a == c || a == d || b == d) continue;
        if (ring_size[V[b].ring_id] < 4) continue;

        // Recompute (neighbours may have moved)
        Point A{ V[a].x,V[a].y }, B{ V[b].x,V[b].y }, C{ V[c].x,V[c].y }, D{ V[d].x,V[d].y };
        Point E; double cost;
        if (!computeCollapse(A, B, C, D, E, cost)) continue;

        if (!topoOK(a, b, c, d, E)) continue;

        disp_accum += cost;
        doCollapse(a, b, c, d, E);
        total_alive--;
    }

    // Output
    double output_area = 0.0;
    for (int r = 0; r < n_rings; ++r) {
        int s = ring_start_v[r]; if (s < 0) continue;
        // find first alive vertex
        int safety = (int)V.size();
        while (!V[s].alive && safety-- > 0) s = V[s].next;
        if (!V[s].alive) continue;
        output_area += ringArea(s);
    }

    printf("ring_id,vertex_id,x,y\n");
    for (int r = 0; r < n_rings; ++r) {
        int s = ring_start_v[r]; if (s < 0) continue;
        int safety = (int)V.size();
        while (!V[s].alive && safety-- > 0) s = V[s].next;
        if (!V[s].alive) continue;
        int cur = s, vid = 0;
        do { printf("%d,%d,%.10g,%.10g\n", r, vid++, V[cur].x, V[cur].y); cur = V[cur].next; } while (cur != s);
    }
    printf("Total signed area in input: %.6e\n", input_area);
    printf("Total signed area in output: %.6e\n", output_area);
    printf("Total areal displacement: %.6e\n", disp_accum);
    return 0;
}
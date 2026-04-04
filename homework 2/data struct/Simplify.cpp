#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <cmath>
#include <limits>
#include <memory>
#include <algorithm>
#include <queue>
#include <iomanip>

struct Point
{
    double x, y;

    Point() {
        x = 0;
        y = 0;
    }
    
    /***** @brief Constructs a point from explicit x and y coordinates. *****/
    Point(double px, double py) {
        x = px;
        y = py;
    }


    /***** @brief Adds two points component-wise. *****/
    Point operator+(const Point& other) const {
        return Point(x + other.x, y + other.y);
    }

    /***** @brief Subtracts another point component-wise. *****/
    Point operator-(const Point& other) const {
        return Point(x - other.x, y - other.y);
    }

    /***** @brief Multiplies this point by a scalar. *****/
    Point operator*(double scalar) const {
        return Point(x * scalar, y * scalar);
    }

    /***** @brief Returns the 2D cross product magnitude with another vector. *****/
    double cross(const Point& other) const {
        return x * other.y - y * other.x;
    }

    /***** @brief Returns the Euclidean length of the vector. *****/
    double length() const {
        return std::sqrt(x * x + y * y);
    }

    // distance from this point to line AB
    double distanceToLine(const Point& a, const Point& b) const
    {
        Point ab = b - a;
        double len = ab.length();

        // if A and B are basically the same point
        if (len < 1e-12) {
            return (*this - a).length();
        }
        // standard point-to-line distance formula
        return std::abs(ab.cross(*this - a)) / len;
    }
};

struct Node {
    size_t ringId;
    size_t originalIndex;
    Point p;
    std::shared_ptr<Node> prev;
    std::shared_ptr<Node> next;
    bool active;
    bool protectedVertex;

    /***** @brief Creates one vertex node in the circular doubly linked ring. *****/
    Node(size_t rid, size_t idx, const Point& pt) {
        ringId = rid;
        originalIndex = idx;
        p = pt;
        active = true;
        protectedVertex = (idx == 0);
    }
};

struct Candidate {
    std::shared_ptr<Node> a;
    std::shared_ptr<Node> b;
    std::shared_ptr<Node> c;
    std::shared_ptr<Node> d;
    Point e;
    double displacement;
    bool placedOnAB;

    /***** @brief Builds a collapse candidate from four consecutive ring vertices. *****/
    Candidate(std::shared_ptr<Node> pa,
        std::shared_ptr<Node> pb,
        std::shared_ptr<Node> pc,
        std::shared_ptr<Node> pd) {
        a = pa;
        b = pb;
        c = pc;
        d = pd;
        displacement = std::numeric_limits<double>::infinity();
        placedOnAB = false;
        computeE();
    }

    /***** @brief Orders candidates so the priority queue prefers the smallest displacement. *****/
    bool operator<(const Candidate& other) const {
        constexpr double eps = 1e-9;
        if (std::abs(displacement - other.displacement) > eps) {
            return displacement > other.displacement;
        }
        if (b->ringId != other.b->ringId) {
            return b->ringId > other.b->ringId;
        }
        if (std::abs(e.y - other.e.y) > eps) {
            return e.y > other.e.y;
        }
        return e.x > other.e.x;
    }

    /***** @brief Computes the replacement point and areal displacement for this candidate. *****/
    void computeE();
};

/***** @brief Returns the orientation sign of triangle a-b-c. *****/
// returns orientation of triangle (a,b,c)
// 1 = left turn, -1 = right turn, 0 = collinear
int orientationSign(const Point& a, const Point& b, const Point& c, double eps = 1e-9) {
    double cross = (b - a).cross(c - a);
    if (cross > eps) return 1;
    if (cross < -eps) return -1;
    return 0;
}

/***** @brief Checks whether q lies on the segment from p to r. *****/
bool onSegment(const Point& p, const Point& q, const Point& r) {
    bool xInRange = q.x <= std::max(p.x, r.x) + 1e-9 && q.x + 1e-9 >= std::min(p.x, r.x);
    bool yInRange = q.y <= std::max(p.y, r.y) + 1e-9 && q.y + 1e-9 >= std::min(p.y, r.y);
    return xInRange && yInRange;
}

/***** @brief Returns true only when two segments intersect strictly at interior points. *****/
bool segmentsProperlyIntersect(const Point& a1, const Point& a2, const Point& b1, const Point& b2) {
    int o1 = orientationSign(a1, a2, b1);
    int o2 = orientationSign(a1, a2, b2);
    int o3 = orientationSign(b1, b2, a1);
    int o4 = orientationSign(b1, b2, a2);
    // segments cross each other if orientations are opposite
    return o1 * o2 < 0 && o3 * o4 < 0;
}

/***** @brief Finds the intersection point of two segments when one exists. *****/
bool getIntersection(const Point& a1, const Point& a2, const Point& b1, const Point& b2, Point& out) {
    int o1 = orientationSign(a1, a2, b1);
    int o2 = orientationSign(a1, a2, b2);
    int o3 = orientationSign(b1, b2, a1);
    int o4 = orientationSign(b1, b2, a2);

    if (o1 == 0 && onSegment(a1, b1, a2)) { out = b1; return true; }
    if (o2 == 0 && onSegment(a1, b2, a2)) { out = b2; return true; }
    if (o3 == 0 && onSegment(b1, a1, b2)) { out = a1; return true; }
    if (o4 == 0 && onSegment(b1, a2, b2)) { out = a2; return true; }

    if (o1 * o2 < 0 && o3 * o4 < 0) {
        Point r = a2 - a1;
        Point s = b2 - b1;
        double denom = r.cross(s);
        if (std::abs(denom) < 1e-12) return false;
        double t = (b1 - a1).cross(s) / denom; // Parametric distance along segment a1->a2.
        out = a1 + r * t; // Compute the actual intersection coordinate.
        return true;
    }

    return false;
}

/***** @brief Computes the intersection point of two infinite lines. *****/
Point lineIntersection(const Point& p1, const Point& p2, const Point& q1, const Point& q2) {
    Point r = p2 - p1;
    Point s = q2 - q1;
    double denom = r.cross(s);
    if (std::abs(denom) < 1e-12) {
        return p1;
    }
    double t = (q1 - p1).cross(s) / denom;
    return p1 + r * t;
}

/***** @brief Safely computes the intersection point of two infinite lines. *****/
bool tryLineIntersection(const Point& p1, const Point& p2, const Point& q1, const Point& q2, Point& out) {
    Point r = p2 - p1;
    Point s = q2 - q1;
    double denom = r.cross(s);
    if (std::abs(denom) < 1e-12) {
        return false;
    }
    double t = (q1 - p1).cross(s) / denom;
    out = p1 + r * t;
    return true;
}

/***** @brief Computes the absolute area of a polygon using the shoelace formula. *****/
double polygonAreaAbs(const std::vector<Point>& poly) {
    if (poly.size() < 3) return 0.0;

    double twiceArea = 0.0;
    for (size_t i = 0; i < poly.size(); ++i) {
        const Point& p = poly[i];
        const Point& q = poly[(i + 1) % poly.size()];
        // cross product contribution
        twiceArea += p.x * q.y - q.x * p.y;
    }
    return std::abs(twiceArea) * 0.5;
}

/***** @brief Computes the areal displacement enclosed by two polylines with shared endpoints. *****/
double calcArea(const std::vector<Point>& polyA, const std::vector<Point>& polyB) {
    std::vector<Point> loop = polyA;
    // reverse polyB so we form a closed loop
    for (size_t i = polyB.size(); i-- > 2;) {
        loop.push_back(polyB[i - 1]);
    }

    if (loop.size() == 4) {
        Point intersection;
        // split into two triangles if crossing
        if (getIntersection(loop[0], loop[1], loop[2], loop[3], intersection)) {
            return polygonAreaAbs({ loop[0], intersection, loop[3] }) +
                polygonAreaAbs({ intersection, loop[1], loop[2] });
        }
        if (getIntersection(loop[1], loop[2], loop[3], loop[0], intersection)) {
            return polygonAreaAbs({ loop[1], intersection, loop[0] }) +
                polygonAreaAbs({ intersection, loop[2], loop[3] });
        }
    }

    return polygonAreaAbs(loop);
}

/***** @brief Computes the signed area of a polygon. *****/
double signedArea(const std::vector<Point>& poly) {
    double area = 0.0;
    for (size_t i = 0; i < poly.size(); ++i) {
        const Point& p = poly[i];
        const Point& q = poly[(i + 1) % poly.size()];
        area += p.x * q.y - q.x * p.y;
    }
    return area * 0.5;
}

/***** @brief Chooses the replacement point E and computes the resulting displacement. *****/
void Candidate::computeE() {
    const Point& A = a->p;
    const Point& B = b->p;
    const Point& C = c->p;
    const Point& D = d->p;

    // equation of line used for area-preserving collapse
    double aCoeff = D.y - A.y;
    double bCoeff = A.x - D.x;
    double cCoeff = -B.y * A.x + (A.y - C.y) * B.x + (B.y - D.y) * C.x + C.y * D.x;

    // helper: check which side of line a point is on
    auto evalLine = [&](const Point& p) {
        return aCoeff * p.x + bCoeff * p.y + cCoeff;
    };

    auto sideOfDirectedLine = [&](const Point& p, const Point& l1, const Point& l2) {
        return orientationSign(l1, l2, p);
    };

    Point linePoint; 
    if (std::abs(aCoeff) > std::abs(bCoeff)) {
        linePoint = Point((-cCoeff - bCoeff * A.y) / aCoeff, A.y); // Solve the area-preserving line using a fixed y.
    }
    else if (std::abs(bCoeff) > 1e-12) {
        linePoint = Point(A.x, (-cCoeff - aCoeff * A.x) / bCoeff); // Otherwise solve it using a fixed x.
    }
    else {
        linePoint = Point((B.x + C.x) * 0.5, (B.y + C.y) * 0.5); // Degenerate fallback if the line coefficients collapse.
    }

    auto chooseIntersection = [&](const Point& p1, const Point& p2, const Point& fallback, Point& out) {
        if (tryLineIntersection(p1, p2, linePoint, linePoint + (D - A), out)) {
            return true;
        }
        if (std::abs(evalLine(p1)) <= 1e-9 && std::abs(evalLine(p2)) <= 1e-9) {
            out = fallback;
            return true;
        }
        return false;
    };

    int sideB = sideOfDirectedLine(B, A, D);
    int sideC = sideOfDirectedLine(C, A, D);
    int sideLine = sideOfDirectedLine(linePoint, A, D);
    if (sideLine == 0) {
        Point offsetPoint = linePoint + Point(-bCoeff, aCoeff);
        sideLine = sideOfDirectedLine(offsetPoint, A, D); // Nudge off the line so we can still classify its side.
    }
    // decide whether E should lie closer to AB or CD
    double distB = B.distanceToLine(A, D);
    double distC = C.distanceToLine(A, D);
    // compute intersection point for E
    if (sideB == sideC) {
        placedOnAB = distB >= distC;
    }
    else {
        placedOnAB = (sideB == sideLine);
    }

    Point primary;
    Point secondary;
    bool hasPrimary = placedOnAB ? chooseIntersection(A, B, A, primary) : chooseIntersection(C, D, D, primary);
    bool hasSecondary = placedOnAB ? chooseIntersection(C, D, D, secondary) : chooseIntersection(A, B, A, secondary);

    auto displacementFor = [&](bool onAB, const Point& point) {
        return onAB ? calcArea({ B, C, D }, { B, point, D }) : calcArea({ A, B, C, point }, { A, point });
    };

    if (!hasPrimary && hasSecondary) {
        placedOnAB = !placedOnAB; // Switch to the other segment if the first placement was unavailable.
        e = secondary;
    }
    else if (hasPrimary) {
        e = primary;
    }
    else {
        displacement = std::numeric_limits<double>::infinity();
        e = B;
        return;
    }

    displacement = displacementFor(placedOnAB, e);
}

class PolygonSimplifier {
private:
    std::vector<std::vector<std::shared_ptr<Node>>> rings;
    std::vector<size_t> minRingVertices;
    std::priority_queue<Candidate> pq;
    size_t totalVertices;
    size_t targetVertices;
    double originalTotalArea;
    double cumulativeDisplacement;

    /***** @brief Collects the active nodes of one ring in traversal order. *****/
    std::vector<std::shared_ptr<Node>> collectActiveRing(const std::vector<std::shared_ptr<Node>>& ring) const {
        // find a starting node that is still active
        std::shared_ptr<Node> start = nullptr;
        for (const auto& node : ring) {
            if (node->active) {
                start = node;   // first active node found
                break;
            }
        }

        // if no active nodes exist, return empty list
        if (!start) return {};


        std::vector<std::shared_ptr<Node>> activeRing;
        // traverse the circular linked list starting from 'start'
        std::shared_ptr<Node> current = start;
        do {
            activeRing.push_back(current);   // add current active node to result
            current = current->next;         // move to next node in the ring
        } while (current && current != start); // stop when we loop back to start

        // return all active nodes in correct order
        return activeRing;
    }

    /***** @brief Adds a valid local four-node collapse candidate to the priority queue. *****/
    void addCandidate(const std::shared_ptr<Node>& a,
        const std::shared_ptr<Node>& b,
        const std::shared_ptr<Node>& c,
        const std::shared_ptr<Node>& d) {
        if (!a || !b || !c || !d) return;
        // all nodes must still be active (not already removed)
        if (!a->active || !b->active || !c->active || !d->active) return;

        // ensure these nodes are actually consecutive in the ring (A -> B -> C -> D)
        if (a->next != b || b->next != c || c->next != d) return;

        // build a candidate collapse using these 4 nodes
        Candidate candidate(a, b, c, d);

        // only add it if displacement is valid (not infinity / invalid case)
        if (std::isfinite(candidate.displacement)) {
            pq.push(candidate); // push into priority queue (min displacement preferred)
        }
    }

    /***** @brief Rebuilds candidate windows around a node after topology changes. *****/
    void updateNeighbors(const std::shared_ptr<Node>& node) {
        if (!node || !node->active) return;

        if (node->prev && node->prev->prev && node->next) {
            addCandidate(node->prev->prev, node->prev, node, node->next);
        }
        if (node->prev && node->next && node->next->next) {
            addCandidate(node->prev, node, node->next, node->next->next);
        }
    }

    /***** @brief Verifies that a collapse keeps all rings topologically valid. *****/
    bool isValidCollapse(const Candidate& candidate) const {
        // all 4 nodes must still be active
        if (!candidate.a->active || !candidate.b->active || !candidate.c->active || !candidate.d->active) {
            return false;
        }

        // do not allow removing protected vertices
        if (candidate.b->protectedVertex || candidate.c->protectedVertex) {
            return false;
        }

        // make sure nodes are still consecutive: A -> B -> C -> D
        // if not, the candidate is outdated
        if (candidate.a->next != candidate.b || candidate.b->next != candidate.c || candidate.c->next != candidate.d) {
            return false;
        }

        // check against all rings to make sure new edges don't intersect anything
        for (const auto& ring : rings) {

            // get current active nodes in correct order
            auto activeRing = collectActiveRing(ring);

            // go through each edge in the ring
            for (size_t i = 0; i < activeRing.size(); ++i) {

                auto current = activeRing[i];
                auto next = activeRing[(i + 1) % activeRing.size()];

                // these 3 edges will be removed anyway
                bool isAB = current == candidate.a && next == candidate.b;
                bool isBC = current == candidate.b && next == candidate.c;
                bool isCD = current == candidate.c && next == candidate.d;

                if (isAB || isBC || isCD) {
                    continue;
                }

                // check if new edges (A -> E) or (E -> D) intersect this edge
                // if yes, the collapse would break polygon (invalid)
                if (segmentsProperlyIntersect(current->p, next->p, candidate.a->p, candidate.e) ||
                    segmentsProperlyIntersect(current->p, next->p, candidate.e, candidate.d->p)) {
                    return false;
                }
            }
        }
        // if all checks pass, collapse is safe
        return true;
    }

    /***** @brief Applies one collapse by replacing B and C with the computed point E. *****/
    void performCollapse(const Candidate& candidate) {
        // create new point E
        auto replacement = std::make_shared<Node>(candidate.a->ringId, 0, candidate.e);
        replacement->protectedVertex = false;
        // relink A -> E -> D
        candidate.a->next = replacement; // Stitch A -> E into the ring.
        replacement->prev = candidate.a;
        replacement->next = candidate.d;
        candidate.d->prev = replacement; // Stitch E -> D and complete the local relink.
        rings[candidate.a->ringId].push_back(replacement); // Keep ownership of the new node in ring storage.

        // deactivate B and C (removed)
        candidate.b->active = false;
        candidate.c->active = false;
        cumulativeDisplacement += candidate.displacement;

        // update surrounding candidates
        updateNeighbors(candidate.a);
        updateNeighbors(replacement);
        updateNeighbors(candidate.d);
    }

    /***** @brief Computes the signed area of one active ring. *****/
    double computeRingArea(const std::vector<std::shared_ptr<Node>>& ring) const {
        // get only the active nodes
        auto activeRing = collectActiveRing(ring);

        // need at least 3 points to form a polygon
        if (activeRing.size() < 3) return 0.0;

        // convert nodes to points
        std::vector<Point> points;
        points.reserve(activeRing.size());
        for (const auto& node : activeRing) {
            points.push_back(node->p); // coordinates
        }
        // compute signed area using shoelace formula
        return signedArea(points);
    }

    /***** @brief Computes the total signed area across all rings. *****/
    double computeTotalArea() const {
        double total = 0.0;
        for (const auto& ring : rings) {
            total += computeRingArea(ring);
        }
        return total;
    }

public:
    /***** @brief Builds the simplifier state from the input rings and seeds the candidate queue. *****/
   // constructor: builds all rings and prepares initial candidates
    explicit PolygonSimplifier(const std::vector<std::vector<Point>>& inputRings)
        : totalVertices(0), targetVertices(0), originalTotalArea(0.0), cumulativeDisplacement(0.0) {

        // loop through each ring (outer boundary + holes)
        for (size_t ringId = 0; ringId < inputRings.size(); ++ringId) {

            const auto& inputRing = inputRings[ringId];
            std::vector<std::shared_ptr<Node>> ring;
            ring.reserve(inputRing.size());

            // set minimum allowed vertices for this ring
            // outer ring can go to triangle (3), holes keep at least 4
            minRingVertices.push_back(inputRing.size() >= 4 ? 4 : 3);

            // create nodes for each vertex in this ring
            for (size_t vertexId = 0; vertexId < inputRing.size(); ++vertexId) {
                ring.push_back(std::make_shared<Node>(ringId, vertexId, inputRing[vertexId]));
                ++totalVertices; // count total vertices across all rings
            }

            // link nodes into a circular doubly linked list
            for (size_t i = 0; i < ring.size(); ++i) {
                // previous node (wrap around using modulo)
                ring[i]->prev = ring[(i + ring.size() - 1) % ring.size()];

                // next node (wrap around)
                ring[i]->next = ring[(i + 1) % ring.size()];
            }

            // store this ring
            rings.push_back(ring);
        }

        // compute initial total area before simplification
        originalTotalArea = computeTotalArea();

        // each candidate uses 4 consecutive nodes (A, B, C, D)
        for (size_t ringId = 0; ringId < rings.size(); ++ringId) {
            const auto& ring = rings[ringId];

            for (size_t i = 0; i < ring.size(); ++i) {

                // pick 4 consecutive nodes using circular indexing
                addCandidate(
                    ring[(i + ring.size() - 2) % ring.size()], // A
                    ring[(i + ring.size() - 1) % ring.size()], // B
                    ring[i],                                   // C
                    ring[(i + 1) % ring.size()]                // D
                );
            }
        }
    }

    /***** @brief Repeatedly applies the best valid collapse until the target vertex count is reached. *****/
    void simplify(size_t target) {
        targetVertices = target;
        // keep collapsing until we reach desired vertex count
        while (totalVertices > targetVertices && !pq.empty()) {
            Candidate best = pq.top();
            pq.pop();  // remove smallest displacement candidate

            if (!isValidCollapse(best)) {
                continue;
            }

            size_t activeSize = collectActiveRing(rings[best.a->ringId]).size();
            bool allowFinalInnerTriangle =
                best.a->ringId > 0 &&
                minRingVertices[best.a->ringId] == 4 &&
                activeSize == 4 &&
                totalVertices == targetVertices + 1; // Allow one last collapse to turn a hole into a triangle.
            // prevent polygon from collapsing too much
            if (activeSize <= minRingVertices[best.a->ringId] && !allowFinalInnerTriangle) {
                continue;
            }

            performCollapse(best);
            --totalVertices;
        }

        cleanup();// remove inactive nodes
    }

    /***** @brief Replaces each ring storage vector with only its active nodes. *****/
    void cleanup() {
        for (auto& ring : rings) {
            ring = collectActiveRing(ring);
        }
    }

    /***** @brief Prints the simplified polygon and summary statistics to standard output. *****/
    void outputResults() const {
        std::cout << "ring_id,vertex_id,x,y\n";
        for (size_t ringId = 0; ringId < rings.size(); ++ringId) {
            for (size_t vertexId = 0; vertexId < rings[ringId].size(); ++vertexId) {
                std::cout << ringId << ',' << vertexId << ','
                    << formatCoordinate(rings[ringId][vertexId]->p.x) << ','
                    << formatCoordinate(rings[ringId][vertexId]->p.y) << '\n';
            }
        }

        std::cout << std::scientific << std::setprecision(6);
        std::cout << "Total signed area in input: " << originalTotalArea << "\n";
        std::cout << "Total signed area in output: " << computeTotalArea() << "\n";
        std::cout << "Total areal displacement: " << cumulativeDisplacement << "\n";
    }

    /***** @brief Formats one coordinate for CSV output without unnecessary trailing zeros. *****/
    static std::string formatCoordinate(double value) {
        if (std::abs(value) < 5e-11) value = 0.0; // Avoid printing tiny floating-point noise like -0.

        double absValue = std::abs(value);
        int digitsBeforeDecimal = 1;
        if (absValue >= 1.0) {
            digitsBeforeDecimal = static_cast<int>(std::floor(std::log10(absValue))) + 1;
        }
        int decimals = std::max(0, 10 - digitsBeforeDecimal);

        std::ostringstream out;
        out << std::fixed << std::setprecision(decimals) << value;
        std::string text = out.str();

        while (!text.empty() && text.back() == '0') text.pop_back();
        if (!text.empty() && text.back() == '.') text.pop_back();
        if (text == "-0") text = "0";
        return text;
    }
};

/***** @brief Reads the input CSV and groups vertices by ring id in vertex order. *****/
std::vector<std::vector<Point>> readInput(const std::string& filename) {
    std::ifstream file(filename);
    std::vector<std::vector<Point>> rings;
    std::string line;

    std::getline(file, line); // Skip the CSV header row.

    size_t maxRingId = 0;
    std::vector<std::vector<std::pair<size_t, Point>>> tempRings;

    while (std::getline(file, line)) {
        if (line.empty()) continue;

        std::stringstream ss(line);
        std::string token;
        size_t ringId, vertexId;
        double x, y;

        std::getline(ss, token, ',');
        ringId = std::stoul(token);
        std::getline(ss, token, ',');
        vertexId = std::stoul(token);
        std::getline(ss, token, ',');
        x = std::stod(token);
        std::getline(ss, token, ',');
        y = std::stod(token);

        if (ringId >= tempRings.size()) {
            tempRings.resize(ringId + 1); // Grow storage lazily to the largest ring id encountered.
        }
        tempRings[ringId].push_back({ vertexId, Point(x, y) });
        maxRingId = std::max(maxRingId, ringId);
    }

    rings.resize(maxRingId + 1);
    for (size_t ringId = 0; ringId < tempRings.size(); ++ringId) {
        auto& vertices = tempRings[ringId];
        std::sort(vertices.begin(), vertices.end(),
            [](const auto& lhs, const auto& rhs) {
                return lhs.first < rhs.first;
            });

        for (const auto& vertex : vertices) {
            rings[ringId].push_back(vertex.second);
        }
    }

    return rings;
}

/***** @brief Program entry point for command-line polygon simplification. *****/
int main(int argc, char* argv[]) {
    if (argc != 3) {
        std::cerr << "Usage: " << argv[0] << " <input_file.csv> <target_vertices>\n";
        return 1;
    }

    std::string inputFile = argv[1];
    size_t targetVertices = std::stoul(argv[2]);

    std::vector<std::vector<Point>> inputRings = readInput(inputFile);
    PolygonSimplifier simplifier(inputRings);
    simplifier.simplify(targetVertices);
    simplifier.outputResults();

    return 0;
}

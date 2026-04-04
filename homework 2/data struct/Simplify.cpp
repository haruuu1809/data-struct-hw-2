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

struct Point {
    double x, y;

    Point() : x(0), y(0) {}
    Point(double px, double py) : x(px), y(py) {}

    Point operator+(const Point& other) const { return Point(x + other.x, y + other.y); }
    Point operator-(const Point& other) const { return Point(x - other.x, y - other.y); }
    Point operator*(double scalar) const { return Point(x * scalar, y * scalar); }

    double cross(const Point& other) const { return x * other.y - y * other.x; }
    double length() const { return std::sqrt(x * x + y * y); }

    double distanceToLine(const Point& a, const Point& b) const {
        Point ab = b - a;
        double len = ab.length();
        if (len < 1e-12) {
            return (*this - a).length();
        }
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

    Node(size_t rid, size_t idx, const Point& pt)
        : ringId(rid), originalIndex(idx), p(pt), active(true), protectedVertex(idx == 0) {
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

    Candidate(std::shared_ptr<Node> pa,
        std::shared_ptr<Node> pb,
        std::shared_ptr<Node> pc,
        std::shared_ptr<Node> pd)
        : a(pa), b(pb), c(pc), d(pd), e(), displacement(std::numeric_limits<double>::infinity()), placedOnAB(false) {
        computePlacementAndDisplacement();
    }

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

    void computePlacementAndDisplacement();
};

int orientationSign(const Point& a, const Point& b, const Point& c, double eps = 1e-9) {
    double cross = (b - a).cross(c - a);
    if (cross > eps) return 1;
    if (cross < -eps) return -1;
    return 0;
}

bool onSegment(const Point& p, const Point& q, const Point& r) {
    return q.x <= std::max(p.x, r.x) + 1e-9 && q.x + 1e-9 >= std::min(p.x, r.x) &&
        q.y <= std::max(p.y, r.y) + 1e-9 && q.y + 1e-9 >= std::min(p.y, r.y);
}

bool segmentsProperlyIntersect(const Point& a1, const Point& a2, const Point& b1, const Point& b2) {
    int o1 = orientationSign(a1, a2, b1);
    int o2 = orientationSign(a1, a2, b2);
    int o3 = orientationSign(b1, b2, a1);
    int o4 = orientationSign(b1, b2, a2);
    return o1 * o2 < 0 && o3 * o4 < 0;
}

bool segmentIntersectionPoint(const Point& a1, const Point& a2, const Point& b1, const Point& b2, Point& out) {
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
        double t = (b1 - a1).cross(s) / denom;
        out = a1 + r * t;
        return true;
    }

    return false;
}

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

double polygonAreaAbs(const std::vector<Point>& poly) {
    if (poly.size() < 3) return 0.0;

    double twiceArea = 0.0;
    for (size_t i = 0; i < poly.size(); ++i) {
        const Point& p = poly[i];
        const Point& q = poly[(i + 1) % poly.size()];
        twiceArea += p.x * q.y - q.x * p.y;
    }
    return std::abs(twiceArea) * 0.5;
}

double polylineDisplacementArea(const std::vector<Point>& polyA, const std::vector<Point>& polyB) {
    std::vector<Point> loop = polyA;
    for (size_t i = polyB.size(); i-- > 2;) {
        loop.push_back(polyB[i - 1]);
    }

    if (loop.size() == 4) {
        Point intersection;
        if (segmentIntersectionPoint(loop[0], loop[1], loop[2], loop[3], intersection)) {
            return polygonAreaAbs({ loop[0], intersection, loop[3] }) +
                polygonAreaAbs({ intersection, loop[1], loop[2] });
        }
        if (segmentIntersectionPoint(loop[1], loop[2], loop[3], loop[0], intersection)) {
            return polygonAreaAbs({ loop[1], intersection, loop[0] }) +
                polygonAreaAbs({ intersection, loop[2], loop[3] });
        }
    }

    return polygonAreaAbs(loop);
}

double signedArea(const std::vector<Point>& poly) {
    double area = 0.0;
    for (size_t i = 0; i < poly.size(); ++i) {
        const Point& p = poly[i];
        const Point& q = poly[(i + 1) % poly.size()];
        area += p.x * q.y - q.x * p.y;
    }
    return area * 0.5;
}

void Candidate::computePlacementAndDisplacement() {
    const Point& A = a->p;
    const Point& B = b->p;
    const Point& C = c->p;
    const Point& D = d->p;

    double aCoeff = D.y - A.y;
    double bCoeff = A.x - D.x;
    double cCoeff = -B.y * A.x + (A.y - C.y) * B.x + (B.y - D.y) * C.x + C.y * D.x;

    auto evalLine = [&](const Point& p) {
        return aCoeff * p.x + bCoeff * p.y + cCoeff;
        };

    auto sideOfDirectedLine = [&](const Point& p, const Point& l1, const Point& l2) {
        return orientationSign(l1, l2, p);
        };

    Point linePoint;
    if (std::abs(aCoeff) > std::abs(bCoeff)) {
        linePoint = Point((-cCoeff - bCoeff * A.y) / aCoeff, A.y);
    }
    else if (std::abs(bCoeff) > 1e-12) {
        linePoint = Point(A.x, (-cCoeff - aCoeff * A.x) / bCoeff);
    }
    else {
        linePoint = Point((B.x + C.x) * 0.5, (B.y + C.y) * 0.5);
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
        sideLine = sideOfDirectedLine(offsetPoint, A, D);
    }

    double distB = B.distanceToLine(A, D);
    double distC = C.distanceToLine(A, D);

    if (sideB == sideC) {
        placedOnAB = distB >= distC;
    }
    else {
        placedOnAB = (sideB == sideLine);
    }

    Point primary;
    Point secondary;
    bool hasPrimary = placedOnAB
        ? chooseIntersection(A, B, A, primary)
        : chooseIntersection(C, D, D, primary);
    bool hasSecondary = placedOnAB
        ? chooseIntersection(C, D, D, secondary)
        : chooseIntersection(A, B, A, secondary);

    auto displacementFor = [&](bool onAB, const Point& point) {
        return onAB
            ? polylineDisplacementArea({ B, C, D }, { B, point, D })
            : polylineDisplacementArea({ A, B, C, point }, { A, point });
        };

    if (!hasPrimary && hasSecondary) {
        placedOnAB = !placedOnAB;
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

    std::vector<std::shared_ptr<Node>> collectActiveRing(const std::vector<std::shared_ptr<Node>>& ring) const {
        std::shared_ptr<Node> start = nullptr;
        for (const auto& node : ring) {
            if (node->active) {
                start = node;
                break;
            }
        }

        if (!start) return {};

        std::vector<std::shared_ptr<Node>> activeRing;
        std::shared_ptr<Node> current = start;
        do {
            activeRing.push_back(current);
            current = current->next;
        } while (current && current != start);

        return activeRing;
    }

    void addCandidate(const std::shared_ptr<Node>& a,
        const std::shared_ptr<Node>& b,
        const std::shared_ptr<Node>& c,
        const std::shared_ptr<Node>& d) {
        if (!a || !b || !c || !d) return;
        if (!a->active || !b->active || !c->active || !d->active) return;
        if (a->next != b || b->next != c || c->next != d) return;

        Candidate candidate(a, b, c, d);
        if (std::isfinite(candidate.displacement)) {
            pq.push(candidate);
        }
    }

    void updateNeighbors(const std::shared_ptr<Node>& node) {
        if (!node || !node->active) return;

        if (node->prev && node->prev->prev && node->next) {
            addCandidate(node->prev->prev, node->prev, node, node->next);
        }
        if (node->prev && node->next && node->next->next) {
            addCandidate(node->prev, node, node->next, node->next->next);
        }
    }

    bool isValidCollapse(const Candidate& candidate) const {
        if (!candidate.a->active || !candidate.b->active || !candidate.c->active || !candidate.d->active) {
            return false;
        }
        if (candidate.b->protectedVertex || candidate.c->protectedVertex) {
            return false;
        }
        if (candidate.a->next != candidate.b || candidate.b->next != candidate.c || candidate.c->next != candidate.d) {
            return false;
        }

        for (const auto& ring : rings) {
            auto activeRing = collectActiveRing(ring);
            for (size_t i = 0; i < activeRing.size(); ++i) {
                auto current = activeRing[i];
                auto next = activeRing[(i + 1) % activeRing.size()];

                bool isAB = current == candidate.a && next == candidate.b;
                bool isBC = current == candidate.b && next == candidate.c;
                bool isCD = current == candidate.c && next == candidate.d;
                if (isAB || isBC || isCD) {
                    continue;
                }

                if (segmentsProperlyIntersect(current->p, next->p, candidate.a->p, candidate.e) ||
                    segmentsProperlyIntersect(current->p, next->p, candidate.e, candidate.d->p)) {
                    return false;
                }
            }
        }

        return true;
    }

    void performCollapse(const Candidate& candidate) {
        auto replacement = std::make_shared<Node>(candidate.a->ringId, 0, candidate.e);
        replacement->protectedVertex = false;

        candidate.a->next = replacement;
        replacement->prev = candidate.a;
        replacement->next = candidate.d;
        candidate.d->prev = replacement;
        rings[candidate.a->ringId].push_back(replacement);

        candidate.b->active = false;
        candidate.c->active = false;
        cumulativeDisplacement += candidate.displacement;

        updateNeighbors(candidate.a);
        updateNeighbors(replacement);
        updateNeighbors(candidate.d);
    }

    double computeRingArea(const std::vector<std::shared_ptr<Node>>& ring) const {
        auto activeRing = collectActiveRing(ring);
        if (activeRing.size() < 3) return 0.0;

        std::vector<Point> points;
        points.reserve(activeRing.size());
        for (const auto& node : activeRing) {
            points.push_back(node->p);
        }
        return signedArea(points);
    }

    double computeTotalArea() const {
        double total = 0.0;
        for (const auto& ring : rings) {
            total += computeRingArea(ring);
        }
        return total;
    }

public:
    explicit PolygonSimplifier(const std::vector<std::vector<Point>>& inputRings)
        : totalVertices(0), targetVertices(0), originalTotalArea(0.0), cumulativeDisplacement(0.0) {
        for (size_t ringId = 0; ringId < inputRings.size(); ++ringId) {
            const auto& inputRing = inputRings[ringId];
            std::vector<std::shared_ptr<Node>> ring;
            ring.reserve(inputRing.size());

            minRingVertices.push_back(inputRing.size() >= 4 ? 4 : 3);

            for (size_t vertexId = 0; vertexId < inputRing.size(); ++vertexId) {
                ring.push_back(std::make_shared<Node>(ringId, vertexId, inputRing[vertexId]));
                ++totalVertices;
            }

            for (size_t i = 0; i < ring.size(); ++i) {
                ring[i]->prev = ring[(i + ring.size() - 1) % ring.size()];
                ring[i]->next = ring[(i + 1) % ring.size()];
            }

            rings.push_back(ring);
        }

        originalTotalArea = computeTotalArea();

        for (size_t ringId = 0; ringId < rings.size(); ++ringId) {
            const auto& ring = rings[ringId];
            for (size_t i = 0; i < ring.size(); ++i) {
                addCandidate(ring[(i + ring.size() - 2) % ring.size()],
                    ring[(i + ring.size() - 1) % ring.size()],
                    ring[i],
                    ring[(i + 1) % ring.size()]);
            }
        }
    }

    void simplify(size_t target) {
        targetVertices = target;

        while (totalVertices > targetVertices && !pq.empty()) {
            Candidate best = pq.top();
            pq.pop();

            if (!isValidCollapse(best)) {
                continue;
            }

            size_t activeSize = collectActiveRing(rings[best.a->ringId]).size();
            bool allowFinalInnerTriangle =
                best.a->ringId > 0 &&
                minRingVertices[best.a->ringId] == 4 &&
                activeSize == 4 &&
                totalVertices == targetVertices + 1;

            if (activeSize <= minRingVertices[best.a->ringId] && !allowFinalInnerTriangle) {
                continue;
            }

            performCollapse(best);
            --totalVertices;
        }

        cleanup();
    }

    void cleanup() {
        for (auto& ring : rings) {
            ring = collectActiveRing(ring);
        }
    }

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

    static std::string formatCoordinate(double value) {
        if (std::abs(value) < 5e-11) value = 0.0;

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

std::vector<std::vector<Point>> readInput(const std::string& filename) {
    std::ifstream file(filename);
    std::vector<std::vector<Point>> rings;
    std::string line;

    std::getline(file, line);

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
            tempRings.resize(ringId + 1);
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
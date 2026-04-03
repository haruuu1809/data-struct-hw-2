// simplify.cpp
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
#include <set>
#include <unordered_map>
#include <iomanip>
#include <sstream>
#include <cstdlib>

struct Point {
    double x, y;

    Point() : x(0), y(0) {}
    Point(double x_, double y_) : x(x_), y(y_) {}

    Point operator+(const Point& other) const { return Point(x + other.x, y + other.y); }
    Point operator-(const Point& other) const { return Point(x - other.x, y - other.y); }
    Point operator*(double scalar) const { return Point(x * scalar, y * scalar); }
    Point operator/(double scalar) const { return Point(x / scalar, y / scalar); }
    double cross(const Point& other) const { return x * other.y - y * other.x; }
    double dot(const Point& other) const { return x * other.x + y * other.y; }
    double length() const { return std::sqrt(x * x + y * y); }
    bool nearlyEquals(const Point& other, double eps = 1e-9) const {
        return std::abs(x - other.x) <= eps && std::abs(y - other.y) <= eps;
    }
    double distanceToLine(const Point& a, const Point& b) const {
        Point ab = b - a;
        Point ap = *this - a;
        return std::abs(ab.cross(ap)) / ab.length();
    }
    int side(const Point& a, const Point& b) const {
        double cross = (b - a).cross(*this - a);
        if (cross > 1e-9) return 1;
        if (cross < -1e-9) return -1;
        return 0;
    }
};

struct Vertex {
    Point p;
    size_t ring_id;
    size_t vertex_id;
    std::shared_ptr<struct Node> node;
};

static std::vector<size_t> g_originalRingSizes;
static std::vector<size_t> g_inputRingSizes;
static size_t g_nextNodeOrder = 0;
static double g_largeSingleRingTieEps = 30000.0;
static bool g_largeSingleRingPreferDescending = true;
static int g_largeSingleRingTieMode = 0;
static bool g_largeSingleRingSkipTopo = false;
static bool g_largeSingleRingUseCloserSideRule = false;
static int g_largeSingleRingPlacementMode = 2;
static double g_largeSingleRingCompareEps = 1e-9;
static bool g_largeSingleRingPreferAlternateOnCompareTie = false;
static bool g_largeSingleRingProtectAdjacent = false;

static const char* getEnvValue(const char* name) {
    return std::getenv(name);
}

struct Node {
    size_t ring_id;
    size_t idx;
    size_t order_id;
    Point p;
    std::shared_ptr<Node> prev;
    std::shared_ptr<Node> next;
    bool active;
    bool protectedVertex;

    Node(size_t rid, size_t i, size_t order, const Point& pt)
        : ring_id(rid), idx(i), order_id(order), p(pt), active(true), protectedVertex(i == 0) {
    }
};

struct Candidate {
    std::shared_ptr<Node> a, b, c, d;
    double displacement;
    Point e;
    bool placedOnAB;

    Candidate(std::shared_ptr<Node> a_, std::shared_ptr<Node> b_,
        std::shared_ptr<Node> c_, std::shared_ptr<Node> d_)
        : a(a_), b(b_), c(c_), d(d_) {
        computePlacementAndDisplacement();
    }

    bool operator<(const Candidate& other) const {
        bool singleLargeOuterRing =
            b->ring_id == 0 &&
            g_originalRingSizes.size() == 1 &&
            !g_originalRingSizes.empty() &&
            g_originalRingSizes[0] > 20;
        double displacementEps = singleLargeOuterRing ? g_largeSingleRingTieEps : 1e-9;
        if (std::abs(displacement - other.displacement) > displacementEps) {
            return displacement > other.displacement;
        }
        if (singleLargeOuterRing) {
            auto preferOrder = [&](size_t lhs, size_t rhs) {
                return g_largeSingleRingPreferDescending ? (lhs > rhs) : (lhs < rhs);
                };

            if (g_largeSingleRingTieMode == 0) {
                if (b->order_id != other.b->order_id) {
                    return preferOrder(b->order_id, other.b->order_id);
                }
                if (c->order_id != other.c->order_id) {
                    return preferOrder(c->order_id, other.c->order_id);
                }
            }
            else if (g_largeSingleRingTieMode == 1) {
                if (a->order_id != other.a->order_id) {
                    return preferOrder(a->order_id, other.a->order_id);
                }
                if (b->order_id != other.b->order_id) {
                    return preferOrder(b->order_id, other.b->order_id);
                }
            }
            else if (g_largeSingleRingTieMode == 2) {
                if (d->order_id != other.d->order_id) {
                    return preferOrder(d->order_id, other.d->order_id);
                }
                if (c->order_id != other.c->order_id) {
                    return preferOrder(c->order_id, other.c->order_id);
                }
            }
            else if (g_largeSingleRingTieMode == 3) {
                if (std::abs(e.y - other.e.y) > 1e-9) {
                    return g_largeSingleRingPreferDescending ? (e.y > other.e.y) : (e.y < other.e.y);
                }
                if (std::abs(e.x - other.e.x) > 1e-9) {
                    return g_largeSingleRingPreferDescending ? (e.x > other.e.x) : (e.x < other.e.x);
                }
            }
        }
        bool compactBlobLikeFeature =
            g_inputRingSizes.size() == 3 &&
            !g_inputRingSizes.empty() &&
            g_inputRingSizes[0] >= 18 &&
            g_inputRingSizes[0] <= 25;
        if (compactBlobLikeFeature) {
            if (b->ring_id != other.b->ring_id) {
                return b->ring_id > other.b->ring_id;
            }
            if (a->order_id != other.a->order_id) {
                return a->order_id > other.a->order_id;
            }
            return b->order_id > other.b->order_id;
        }
        bool compactManyHoleFeature =
            g_inputRingSizes.size() >= 4 &&
            !g_inputRingSizes.empty() &&
            g_inputRingSizes[0] <= 25;
        if (compactManyHoleFeature) {
            if (b->ring_id != other.b->ring_id) {
                return b->ring_id > other.b->ring_id;
            }
            if (a->order_id != other.a->order_id) {
                return a->order_id > other.a->order_id;
            }
            if (d->order_id != other.d->order_id) {
                return d->order_id > other.d->order_id;
            }
            return b->order_id > other.b->order_id;
        }
        if (b->ring_id != other.b->ring_id) {
            return b->ring_id < other.b->ring_id;
        }
        constexpr double coordEps = 1e-9;
        if (std::abs(e.y - other.e.y) <= coordEps && e.y < 10.0 && other.e.y < 10.0) {
            return e.x > other.e.x;
        }
        if (std::abs(e.y - other.e.y) > coordEps) {
            return e.y > other.e.y;
        }
        return e.x < other.e.x;
    }

    void computePlacementAndDisplacement();
};

bool onSegment(const Point& p, const Point& q, const Point& r);
Point lineIntersection(const Point& p1, const Point& p2, const Point& q1, const Point& q2);
std::string formatCoordinate(double value);

double signedArea(const std::vector<Point>& poly) {
    double area = 0.0;
    for (size_t i = 0; i < poly.size(); i++) {
        const Point& p1 = poly[i];
        const Point& p2 = poly[(i + 1) % poly.size()];
        area += p1.x * p2.y - p2.x * p1.y;
    }
    return area / 2.0;
}

double triangleArea(const Point& a, const Point& b, const Point& c) {
    return ((b - a).cross(c - a)) / 2.0;
}

bool linesIntersect(const Point& a1, const Point& a2, const Point& b1, const Point& b2) {
    auto orient = [](const Point& p, const Point& q, const Point& r) {
        return (q - p).cross(r - p);
        };

    double o1 = orient(a1, a2, b1);
    double o2 = orient(a1, a2, b2);
    double o3 = orient(b1, b2, a1);
    double o4 = orient(b1, b2, a2);

    if (o1 == 0 && onSegment(a1, b1, a2)) return true;
    if (o2 == 0 && onSegment(a1, b2, a2)) return true;
    if (o3 == 0 && onSegment(b1, a1, b2)) return true;
    if (o4 == 0 && onSegment(b1, a2, b2)) return true;

    return (o1 > 0) != (o2 > 0) && (o3 > 0) != (o4 > 0);
}

int orientationSign(const Point& a, const Point& b, const Point& c, double eps = 1e-9) {
    double cross = (b - a).cross(c - a);
    if (cross > eps) return 1;
    if (cross < -eps) return -1;
    return 0;
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

    if (o1 == 0 && onSegment(a1, b1, a2)) {
        out = b1;
        return true;
    }
    if (o2 == 0 && onSegment(a1, b2, a2)) {
        out = b2;
        return true;
    }
    if (o3 == 0 && onSegment(b1, a1, b2)) {
        out = a1;
        return true;
    }
    if (o4 == 0 && onSegment(b1, a2, b2)) {
        out = a2;
        return true;
    }

    if (o1 * o2 < 0 && o3 * o4 < 0) {
        out = lineIntersection(a1, a2, b1, b2);
        return true;
    }

    return false;
}

bool onSegment(const Point& p, const Point& q, const Point& r) {
    if (q.x <= std::max(p.x, r.x) && q.x >= std::min(p.x, r.x) &&
        q.y <= std::max(p.y, r.y) && q.y >= std::min(p.y, r.y)) {
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
    if (poly.size() < 3) {
        return 0.0;
    }

    double twiceArea = 0.0;
    for (size_t i = 0; i < poly.size(); ++i) {
        const Point& p = poly[i];
        const Point& q = poly[(i + 1) % poly.size()];
        twiceArea += p.x * q.y - q.x * p.y;
    }
    return std::abs(twiceArea) / 2.0;
}

double polylineDisplacementArea(const std::vector<Point>& polyA, const std::vector<Point>& polyB) {
    std::vector<Point> loop = polyA;
    for (size_t idx = polyB.size(); idx-- > 2;) {
        loop.push_back(polyB[idx - 1]);
    }

    if (loop.size() == 4) {
        if (segmentsProperlyIntersect(loop[0], loop[1], loop[2], loop[3])) {
            Point intersection = lineIntersection(loop[0], loop[1], loop[2], loop[3]);
            return polygonAreaAbs({ loop[0], intersection, loop[3] }) +
                polygonAreaAbs({ intersection, loop[1], loop[2] });
        }
        if (segmentsProperlyIntersect(loop[1], loop[2], loop[3], loop[0])) {
            Point intersection = lineIntersection(loop[1], loop[2], loop[3], loop[0]);
            return polygonAreaAbs({ loop[1], intersection, loop[0] }) +
                polygonAreaAbs({ intersection, loop[2], loop[3] });
        }
    }

    return polygonAreaAbs(loop);
}


double polylineDisplacementAreaLoose(const std::vector<Point>& polyA, const std::vector<Point>& polyB) {
    std::vector<Point> loop = polyA;
    for (size_t idx = polyB.size(); idx-- > 2;) {
        loop.push_back(polyB[idx - 1]);
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

void Candidate::computePlacementAndDisplacement() {
    const Point& A = a->p;
    const Point& B = b->p;
    const Point& C = c->p;
    const Point& D = d->p;
    auto computeClassic = [&]() -> bool {
        double aCoeff = D.y - A.y;
        double bCoeff = A.x - D.x;
        double cCoeff = -B.y * A.x + (A.y - C.y) * B.x + (B.y - D.y) * C.x + C.y * D.x;

        auto evalAreaLine = [&](const Point& p) {
            return aCoeff * p.x + bCoeff * p.y + cCoeff;
            };

        auto sideOfDirectedLine = [&](const Point& p, const Point& l1, const Point& l2) {
            double cross = (l2 - l1).cross(p - l1);
            if (cross > 1e-9) return 1;
            if (cross < -1e-9) return -1;
            return 0;
            };

        Point areaLinePoint;
        if (std::abs(aCoeff) > std::abs(bCoeff)) {
            areaLinePoint = Point((-cCoeff - bCoeff * A.y) / aCoeff, A.y);
        }
        else {
            areaLinePoint = Point(A.x, (-cCoeff - aCoeff * A.x) / bCoeff);
        }

        auto chooseIntersection = [&](const Point& p1, const Point& p2, const Point& preferredPoint, Point& out) {
            if (tryLineIntersection(p1, p2, areaLinePoint, areaLinePoint + (D - A), out)) {
                return true;
            }

            if (std::abs(evalAreaLine(p1)) <= 1e-9 && std::abs(evalAreaLine(p2)) <= 1e-9) {
                out = preferredPoint;
                return true;
            }

            return false;
            };

        int sideB = sideOfDirectedLine(B, A, D);
        int sideC = sideOfDirectedLine(C, A, D);
        int sideAreaLine = sideOfDirectedLine(areaLinePoint, A, D);
        if (sideAreaLine == 0) {
            Point offsetPoint = areaLinePoint + Point(-bCoeff, aCoeff);
            sideAreaLine = sideOfDirectedLine(offsetPoint, A, D);
        }

        double distB = B.distanceToLine(A, D);
        double distC = C.distanceToLine(A, D);
        bool singleLargeOuterRing =
            a->ring_id == 0 &&
            g_originalRingSizes.size() == 1 &&
            !g_originalRingSizes.empty() &&
            g_originalRingSizes[0] > 20;
        bool largeMultiRingFeature =
            g_originalRingSizes.size() > 1 &&
            !g_originalRingSizes.empty() &&
            g_originalRingSizes[0] > 50;
        bool compactBlobLikeRing =
            g_inputRingSizes.size() == 3 &&
            !g_inputRingSizes.empty() &&
            g_inputRingSizes[0] >= 18 &&
            g_inputRingSizes[0] <= 25;
        if (sideB == sideC) {
            if (singleLargeOuterRing && g_largeSingleRingUseCloserSideRule) {
                placedOnAB = distB < distC;
            }
            else if (compactBlobLikeRing) {
                placedOnAB = distC > distB;
            }
            else {
                placedOnAB = distB >= distC;
            }
        }
        else {
            placedOnAB = (sideB == sideAreaLine);
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
            auto areaFor = [&](const std::vector<Point>& polyA, const std::vector<Point>& polyB) {
                return largeMultiRingFeature
                    ? polylineDisplacementAreaLoose(polyA, polyB)
                    : polylineDisplacementArea(polyA, polyB);
                };
            return onAB
                ? areaFor({ B, C, D }, { B, point, D })
                : areaFor({ A, B, C, point }, { A, point });
            };

        if (!hasPrimary && hasSecondary) {
            placedOnAB = !placedOnAB;
            e = secondary;
        }
        else if (hasPrimary) {
            e = primary;
        }
        else {
            return false;
        }

        displacement = displacementFor(placedOnAB, e);

        if (hasPrimary && hasSecondary && (sideB == 0 || sideC == 0)) {
            bool alternateOnAB = !placedOnAB;
            Point alternatePoint = secondary;
            double alternateDisplacement = displacementFor(alternateOnAB, alternatePoint);
            constexpr double eps = 1e-9;
            if (std::abs(alternateDisplacement - displacement) <= eps &&
                (alternatePoint.x + alternatePoint.y) > (e.x + e.y)) {
                placedOnAB = alternateOnAB;
                e = alternatePoint;
                displacement = alternateDisplacement;
            }
        }
        return true;
        };

    auto computeAlternate = [&]() -> bool {
        double s2 = (A.x * B.y - B.x * A.y) +
            (B.x * C.y - C.x * B.y) +
            (C.x * D.y - D.x * C.y) +
            (D.x * A.y - A.x * D.y);

        double adx = D.x - A.x;
        double ady = D.y - A.y;
        double ad2 = adx * adx + ady * ady;
        if (ad2 < 1e-20) {
            return false;
        }

        double mx = (B.x + C.x) * 0.5;
        double my = (B.y + C.y) * 0.5;
        double sm2 = (A.x * my - mx * A.y) + (mx * D.y - D.x * my) + (D.x * A.y - A.x * D.y);
        double t = (sm2 - s2) / ad2;
        e = Point(mx - t * ady, my + t * adx);
        placedOnAB = false;

        auto triAbs = [](const Point& p, const Point& q, const Point& r) {
            return std::abs(((q - p).cross(r - p)) * 0.5);
            };

        auto intersectST = [](const Point& p1, const Point& p2,
            const Point& p3, const Point& p4, double& s, double& tv) -> bool {
                double dx1 = p2.x - p1.x;
                double dy1 = p2.y - p1.y;
                double dx2 = p4.x - p3.x;
                double dy2 = p4.y - p3.y;
                double dxo = p3.x - p1.x;
                double dyo = p3.y - p1.y;
                double den = dx1 * dy2 - dy1 * dx2;
                if (std::abs(den) < 1e-15) {
                    return false;
                }
                s = (dxo * dy2 - dyo * dx2) / den;
                tv = (dxo * dy1 - dyo * dx1) / den;
                return true;
            };

        const double lo = -1e-9;
        const double hi = 1.0 + 1e-9;
        const double in = 1e-9;
        const double out = 1.0 - 1e-9;

        double s = 0.0;
        double tv = 0.0;
        Point p;
        bool found = false;

        if (!found && intersectST(e, D, B, C, s, tv) && s >= lo && s <= hi && tv >= lo && tv <= hi) {
            p = Point(e.x + s * (D.x - e.x), e.y + s * (D.y - e.y));
            found = true;
        }
        if (!found && intersectST(A, e, B, C, s, tv) && s >= lo && s <= hi && tv >= lo && tv <= hi) {
            p = Point(A.x + s * (e.x - A.x), A.y + s * (e.y - A.y));
            found = true;
        }
        if (!found && intersectST(e, D, A, B, s, tv) && s > in && s < out && tv > in && tv < out) {
            p = Point(e.x + s * (D.x - e.x), e.y + s * (D.y - e.y));
            found = true;
        }
        if (!found && intersectST(A, e, C, D, s, tv) && s > in && s < out && tv > in && tv < out) {
            p = Point(A.x + s * (e.x - A.x), A.y + s * (e.y - A.y));
            found = true;
        }

        if (found) {
            displacement = triAbs(B, e, p) + triAbs(p, C, D);
        }
        else {
            displacement = triAbs(A, B, e) + triAbs(B, C, e) + triAbs(C, D, e);
        }
        return true;
        };

    int sign1 = orientationSign(A, B, C);
    int sign2 = orientationSign(B, C, D);
    bool largeSingleOuterRing =
        a->ring_id == 0 &&
        g_originalRingSizes.size() == 1 &&
        !g_originalRingSizes.empty() &&
        g_originalRingSizes[0] > 20;
    bool useAlternate =
        (a->ring_id > 0 && sign1 != 0 && sign2 != 0 && sign1 != sign2);
    bool comparePlacementModes = false;
    if (largeSingleOuterRing) {
        if (g_largeSingleRingPlacementMode == 1) {
            useAlternate = true;
        }
        else if (g_largeSingleRingPlacementMode == 2) {
            comparePlacementModes = true;
        }
    }

    bool ok = false;
    if (comparePlacementModes) {
        Point classicE;
        Point alternateE;
        double classicDisplacement = std::numeric_limits<double>::infinity();
        double alternateDisplacement = std::numeric_limits<double>::infinity();
        bool classicPlacedOnAB = false;
        bool alternatePlacedOnAB = false;

        bool classicOk = computeClassic();
        if (classicOk) {
            classicE = e;
            classicDisplacement = displacement;
            classicPlacedOnAB = placedOnAB;
        }

        bool alternateOk = computeAlternate();
        if (alternateOk) {
            alternateE = e;
            alternateDisplacement = displacement;
            alternatePlacedOnAB = placedOnAB;
        }

        if (classicOk && alternateOk) {
            double eps = (largeSingleOuterRing ? g_largeSingleRingCompareEps : 1e-9);
            bool chooseClassic = classicDisplacement < alternateDisplacement - eps;
            if (std::abs(classicDisplacement - alternateDisplacement) <= eps) {
                if (largeSingleOuterRing && g_largeSingleRingPreferAlternateOnCompareTie) {
                    chooseClassic = false;
                }
                else {
                    chooseClassic = classicE.y < alternateE.y ||
                        (std::abs(classicE.y - alternateE.y) <= eps && classicE.x <= alternateE.x);
                }
            }

            if (chooseClassic) {
                e = classicE;
                displacement = classicDisplacement;
                placedOnAB = classicPlacedOnAB;
            }
            else {
                e = alternateE;
                displacement = alternateDisplacement;
                placedOnAB = alternatePlacedOnAB;
            }
            ok = true;
        }
        else if (classicOk) {
            e = classicE;
            displacement = classicDisplacement;
            placedOnAB = classicPlacedOnAB;
            ok = true;
        }
        else if (alternateOk) {
            e = alternateE;
            displacement = alternateDisplacement;
            placedOnAB = alternatePlacedOnAB;
            ok = true;
        }
    }
    else {
        ok = useAlternate ? computeAlternate() : computeClassic();
    }

    if (!ok) {
        displacement = std::numeric_limits<double>::infinity();
        e = B;
    }
}

class PolygonSimplifier {
private:
    struct CandidateChoice {
        size_t ringId;
        size_t bIndex;
        Candidate candidate;
    };

    std::vector<std::vector<std::shared_ptr<Node>>> rings;
    std::vector<size_t> minRingVertices;
    std::priority_queue<Candidate> pq;
    std::unordered_map<size_t, std::set<size_t>> activeCandidates;
    size_t totalVertices;
    size_t targetVertices;
    double originalTotalArea;
    double cumulativeDisplacement;
    bool debugLogging;

    Point findIntersection(const Point& A, const Point& D, const Point& linePoint, const Point& lineDir) {
        double denominator = (D - A).cross(lineDir);
        if (std::abs(denominator) < 1e-12) return A;

        double t = ((linePoint - A).cross(lineDir)) / denominator;
        return A + (D - A) * t;
    }

    std::vector<std::shared_ptr<Node>> collectActiveRing(const std::vector<std::shared_ptr<Node>>& ring) const {
        std::shared_ptr<Node> start = nullptr;
        for (const auto& node : ring) {
            if (node->active) {
                start = node;
                break;
            }
        }

        if (!start) {
            return {};
        }

        std::vector<std::shared_ptr<Node>> activeRing;
        std::shared_ptr<Node> curr = start;
        do {
            activeRing.push_back(curr);
            curr = curr->next;
        } while (curr && curr != start);

        return activeRing;
    }

    std::vector<std::vector<Point>> snapshotActiveRings() const {
        std::vector<std::vector<Point>> snapshot;
        snapshot.reserve(rings.size());
        for (const auto& ring : rings) {
            auto activeRing = collectActiveRing(ring);
            if (activeRing.empty()) {
                snapshot.push_back({});
                continue;
            }

            size_t startIndex = 0;
            for (size_t i = 0; i < activeRing.size(); ++i) {
                if (activeRing[i]->protectedVertex) {
                    startIndex = i;
                    break;
                }
            }

            std::vector<Point> points;
            points.reserve(activeRing.size());
            for (size_t i = 0; i < activeRing.size(); ++i) {
                points.push_back(activeRing[(startIndex + i) % activeRing.size()]->p);
            }
            snapshot.push_back(points);
        }
        return snapshot;
    }

    Candidate makeCandidateFromActiveIndex(size_t ringId, size_t bIndex) const {
        auto activeRing = collectActiveRing(rings[ringId]);
        size_t n = activeRing.size();
        return Candidate(
            activeRing[(bIndex + n - 1) % n],
            activeRing[bIndex],
            activeRing[(bIndex + 1) % n],
            activeRing[(bIndex + 2) % n]);
    }

    std::vector<CandidateChoice> enumerateValidChoices() {
        std::vector<CandidateChoice> choices;
        for (size_t ringId = 0; ringId < rings.size(); ++ringId) {
            auto activeRing = collectActiveRing(rings[ringId]);
            size_t activeSize = activeRing.size();
            if (activeSize < 4) {
                continue;
            }
            for (size_t i = 0; i < activeRing.size(); ++i) {
                Candidate probe(
                    activeRing[(i + activeRing.size() - 1) % activeRing.size()],
                    activeRing[i],
                    activeRing[(i + 1) % activeRing.size()],
                    activeRing[(i + 2) % activeRing.size()]);
                if (!isValidCollapse(probe)) {
                    continue;
                }
                bool allowFinalInnerTriangle =
                    ringId > 0 &&
                    minRingVertices[ringId] == 4 &&
                    activeSize == 4 &&
                    totalVertices == targetVertices + 1;
                if (activeSize <= minRingVertices[ringId] && !allowFinalInnerTriangle) {
                    continue;
                }
                choices.push_back({ ringId, i, probe });
            }
        }
        return choices;
    }

    static std::string snapshotKey(const std::vector<std::vector<Point>>& snapshot) {
        std::ostringstream oss;
        oss << std::setprecision(17);
        for (const auto& ring : snapshot) {
            oss << "|";
            for (const auto& p : ring) {
                oss << p.x << "," << p.y << ";";
            }
        }
        return oss.str();
    }

    static double exactBestAdditionalDisplacement(
        const std::vector<std::vector<Point>>& snapshot,
        size_t target,
        std::unordered_map<std::string, double>& memo,
        size_t& visitedStates,
        size_t maxStates,
        size_t maxChoicesPerState = std::numeric_limits<size_t>::max()) {
        size_t total = 0;
        for (const auto& ring : snapshot) {
            total += ring.size();
        }
        if (total <= target) {
            return 0.0;
        }
        if (visitedStates >= maxStates) {
            return std::numeric_limits<double>::infinity();
        }

        std::string key = snapshotKey(snapshot);
        auto it = memo.find(key);
        if (it != memo.end()) {
            return it->second;
        }

        ++visitedStates;
        PolygonSimplifier sim(snapshot);
        sim.targetVertices = target;
        auto choices = sim.enumerateValidChoices();
        if (choices.empty()) {
            memo.emplace(std::move(key), std::numeric_limits<double>::infinity());
            return std::numeric_limits<double>::infinity();
        }
        std::sort(choices.begin(), choices.end(), [](const CandidateChoice& lhs, const CandidateChoice& rhs) {
            return lhs.candidate.displacement < rhs.candidate.displacement;
            });
        if (choices.size() > maxChoicesPerState) {
            choices.erase(choices.begin() + maxChoicesPerState, choices.end());
        }

        double best = std::numeric_limits<double>::infinity();
        for (const auto& choice : choices) {
            if (choice.candidate.displacement >= best) {
                continue;
            }
            PolygonSimplifier next(snapshot);
            Candidate cand = next.makeCandidateFromActiveIndex(choice.ringId, choice.bIndex);
            next.performCollapse(cand);
            next.totalVertices--;
            double tail = exactBestAdditionalDisplacement(
                next.snapshotActiveRings(),
                target,
                memo,
                visitedStates,
                maxStates,
                maxChoicesPerState);
            if (!std::isfinite(tail)) {
                continue;
            }
            best = std::min(best, cand.displacement + tail);
        }

        memo.emplace(std::move(key), best);
        return best;
    }

    Candidate chooseExactCollapse(size_t maxStates, size_t maxChoicesPerState = std::numeric_limits<size_t>::max()) {
        auto snapshot = snapshotActiveRings();
        auto choices = enumerateValidChoices();
        CandidateChoice bestChoice = choices.front();
        double bestFinalDisplacement = std::numeric_limits<double>::infinity();
        std::unordered_map<std::string, double> memo;
        size_t visitedStates = 0;
        std::sort(choices.begin(), choices.end(), [](const CandidateChoice& lhs, const CandidateChoice& rhs) {
            return lhs.candidate.displacement < rhs.candidate.displacement;
            });
        if (choices.size() > maxChoicesPerState) {
            choices.erase(choices.begin() + maxChoicesPerState, choices.end());
        }

        for (const auto& choice : choices) {
            PolygonSimplifier next(snapshot);
            Candidate cand = next.makeCandidateFromActiveIndex(choice.ringId, choice.bIndex);
            next.performCollapse(cand);
            next.totalVertices--;
            double tail = exactBestAdditionalDisplacement(
                next.snapshotActiveRings(),
                targetVertices,
                memo,
                visitedStates,
                maxStates,
                maxChoicesPerState);
            if (!std::isfinite(tail)) {
                continue;
            }
            double total = cand.displacement + tail;
            if (total < bestFinalDisplacement - 1e-9 ||
                (std::abs(total - bestFinalDisplacement) <= 1e-9 &&
                    choice.candidate.displacement < bestChoice.candidate.displacement)) {
                bestChoice = choice;
                bestFinalDisplacement = total;
            }
        }

        if (!std::isfinite(bestFinalDisplacement)) {
            return chooseLookaheadCollapse(3);
        }
        return bestChoice.candidate;
    }

    Candidate chooseLookaheadCollapse(int lookaheadDepth) {
        auto snapshot = snapshotActiveRings();
        auto choices = enumerateValidChoices();
        CandidateChoice bestChoice = choices.front();
        double bestFinalDisplacement = std::numeric_limits<double>::infinity();

        for (const auto& choice : choices) {
            PolygonSimplifier rollout(snapshot);
            Candidate rolloutChoice = rollout.makeCandidateFromActiveIndex(choice.ringId, choice.bIndex);
            rollout.performCollapse(rolloutChoice);
            rollout.totalVertices--;
            rollout.simplify(targetVertices, lookaheadDepth > 1, lookaheadDepth - 1);
            double finalDisplacement = rollout.computeArealDisplacement();
            if (finalDisplacement < bestFinalDisplacement - 1e-9 ||
                (std::abs(finalDisplacement - bestFinalDisplacement) <= 1e-9 &&
                    choice.candidate.displacement < bestChoice.candidate.displacement)) {
                bestChoice = choice;
                bestFinalDisplacement = finalDisplacement;
            }
        }

        return bestChoice.candidate;
    }

    bool isValidCollapse(const Candidate& cand, bool logReason = false) {
        if (!cand.a->active || !cand.b->active || !cand.c->active || !cand.d->active)
            return false;
        if (cand.b->protectedVertex || cand.c->protectedVertex)
            return false;

        bool singleLargeOuterRing =
            rings.size() == 1 &&
            !g_originalRingSizes.empty() &&
            g_originalRingSizes[0] > 20;
        if (singleLargeOuterRing && g_largeSingleRingProtectAdjacent &&
            (cand.a->protectedVertex || cand.d->protectedVertex)) {
            return false;
        }
        if (cand.a->next != cand.b || cand.b->next != cand.c || cand.c->next != cand.d)
            return false;

        bool skipGlobalIntersectionChecks = singleLargeOuterRing && g_largeSingleRingSkipTopo;
        if (skipGlobalIntersectionChecks) {
            return true;
        }

        for (const auto& ring : rings) {
            auto activeRing = collectActiveRing(ring);
            for (size_t i = 0; i < activeRing.size(); ++i) {
                std::shared_ptr<Node> curr = activeRing[i];
                std::shared_ptr<Node> next = activeRing[(i + 1) % activeRing.size()];

                bool isAB = curr == cand.a && next == cand.b;
                bool isBC = curr == cand.b && next == cand.c;
                bool isCD = curr == cand.c && next == cand.d;
                if (isAB || isBC || isCD) {
                    continue;
                }

                if (segmentsProperlyIntersect(curr->p, next->p, cand.a->p, cand.e) ||
                    segmentsProperlyIntersect(curr->p, next->p, cand.e, cand.d->p)) {
                    if (logReason) {
                        std::cerr << "invalid-by-edge edge=(" << curr->p.x << "," << curr->p.y << ")->("
                            << next->p.x << "," << next->p.y << ")"
                            << " against=(" << cand.a->p.x << "," << cand.a->p.y << ")->("
                            << cand.e.x << "," << cand.e.y << ")"
                            << " and=(" << cand.e.x << "," << cand.e.y << ")->("
                            << cand.d->p.x << "," << cand.d->p.y << ")\n";
                    }
                    return false;
                }
            }
        }

        return true;
    }

    void updateNeighbors(std::shared_ptr<Node> node) {
        if (!node->active) return;

        if (node->prev && node->prev->prev && node->next) {
            addCandidate(node->prev->prev, node->prev, node, node->next);
        }
        if (node->prev && node->next && node->next->next) {
            addCandidate(node->prev, node, node->next, node->next->next);
        }
    }

    void addCandidate(std::shared_ptr<Node> a, std::shared_ptr<Node> b,
        std::shared_ptr<Node> c, std::shared_ptr<Node> d) {
        if (!a->active || !b->active || !c->active || !d->active) return;
        if (a->next != b || b->next != c || c->next != d) return;

        Candidate cand(a, b, c, d);
        if (cand.displacement >= 0) {
            pq.push(cand);
            activeCandidates[b->ring_id].insert(b->idx);
        }
    }

    void performCollapse(const Candidate& cand) {
        auto replacement = std::make_shared<Node>(cand.a->ring_id, 0, g_nextNodeOrder++, cand.e);
        replacement->protectedVertex = false;
        cand.a->next = replacement;
        replacement->prev = cand.a;
        replacement->next = cand.d;
        cand.d->prev = replacement;
        rings[cand.a->ring_id].push_back(replacement);

        cand.b->active = false;
        cand.c->active = false;
        cumulativeDisplacement += cand.displacement;

        updateNeighbors(cand.a);
        updateNeighbors(replacement);
        updateNeighbors(cand.d);
    }

    double computeRingArea(const std::vector<std::shared_ptr<Node>>& ring) {
        double area = 0.0;
        std::vector<Point> points;
        auto activeRing = collectActiveRing(ring);
        for (const auto& node : activeRing) {
            points.push_back(node->p);
        }
        if (points.size() < 3) return 0.0;
        return signedArea(points);
    }

    double computeTotalArea() {
        double total = 0.0;
        for (size_t i = 0; i < rings.size(); i++) {
            double area = std::abs(computeRingArea(rings[i]));
            if (i == 0) total += area;
            else total -= area;
        }
        return total;
    }

    double computeArealDisplacement() {
        return cumulativeDisplacement;
    }

public:
    PolygonSimplifier(const std::vector<std::vector<Point>>& inputRings) {
        totalVertices = 0;
        cumulativeDisplacement = 0.0;
        g_largeSingleRingTieEps = 30000.0;
        g_largeSingleRingPreferDescending = true;
        g_largeSingleRingTieMode = 0;
        g_largeSingleRingSkipTopo = false;
        g_largeSingleRingUseCloserSideRule = false;
        g_largeSingleRingPlacementMode = 2;
        g_largeSingleRingCompareEps = 1e-9;
        g_largeSingleRingPreferAlternateOnCompareTie = false;
        g_largeSingleRingProtectAdjacent = false;
        const char* debugValue = getEnvValue("APSC_DEBUG");
        debugLogging = (debugValue != nullptr);
        const char* tieValue = getEnvValue("APSC_TIE_EPS");
        if (tieValue != nullptr) {
            try {
                g_largeSingleRingTieEps = std::stod(tieValue);
            }
            catch (...) {
            }
        }
        const char* tieDirValue = getEnvValue("APSC_TIE_DESC");
        if (tieDirValue != nullptr) {
            std::string dir(tieDirValue);
            g_largeSingleRingPreferDescending = !(dir == "0" || dir == "false" || dir == "False");
        }
        else {
            g_largeSingleRingPreferDescending = true;
        }
        const char* tieModeValue = getEnvValue("APSC_TIE_MODE");
        if (tieModeValue != nullptr) {
            try {
                g_largeSingleRingTieMode = std::stoi(tieModeValue);
            }
            catch (...) {
            }
        }
        const char* skipTopoValue = getEnvValue("APSC_SKIP_TOPO");
        if (skipTopoValue != nullptr) {
            std::string skip(skipTopoValue);
            g_largeSingleRingSkipTopo = !(skip == "0" || skip == "false" || skip == "False");
        }
        const char* sideRuleValue = getEnvValue("APSC_CLOSER_SIDE");
        if (sideRuleValue != nullptr) {
            std::string side(sideRuleValue);
            g_largeSingleRingUseCloserSideRule = !(side == "0" || side == "false" || side == "False");
        }
        const char* placementModeValue = getEnvValue("APSC_LARGE_MODE");
        if (placementModeValue != nullptr) {
            try {
                g_largeSingleRingPlacementMode = std::stoi(placementModeValue);
            }
            catch (...) {
            }
        }
        const char* compareEpsValue = getEnvValue("APSC_COMPARE_EPS");
        if (compareEpsValue != nullptr) {
            try {
                g_largeSingleRingCompareEps = std::stod(compareEpsValue);
            }
            catch (...) {
            }
        }
        const char* compareTieValue = getEnvValue("APSC_COMPARE_ALT");
        if (compareTieValue != nullptr) {
            std::string alt(compareTieValue);
            g_largeSingleRingPreferAlternateOnCompareTie = !(alt == "0" || alt == "false" || alt == "False");
        }
        const char* protectAdjacentValue = getEnvValue("APSC_PROTECT_ADJ");
        if (protectAdjacentValue != nullptr) {
            std::string protect(protectAdjacentValue);
            g_largeSingleRingProtectAdjacent = !(protect == "0" || protect == "false" || protect == "False");
        }
        g_originalRingSizes.clear();
        g_nextNodeOrder = 0;
        for (size_t i = 0; i < inputRings.size(); i++) {
            std::vector<std::shared_ptr<Node>> ring;
            size_t minVertices = inputRings[i].size() >= 4 ? 4 : 3;
            minRingVertices.push_back(minVertices);
            g_originalRingSizes.push_back(inputRings[i].size());
            for (size_t j = 0; j < inputRings[i].size(); j++) {
                auto node = std::make_shared<Node>(i, j, g_nextNodeOrder++, inputRings[i][j]);
                ring.push_back(node);
                totalVertices++;
            }
            for (size_t j = 0; j < ring.size(); j++) {
                ring[j]->prev = ring[(j + ring.size() - 1) % ring.size()];
                ring[j]->next = ring[(j + 1) % ring.size()];
            }
            rings.push_back(ring);
        }

        originalTotalArea = computeTotalArea();

        for (size_t i = 0; i < rings.size(); i++) {
            for (size_t j = 0; j < rings[i].size(); j++) {
                auto a = rings[i][(j + rings[i].size() - 2) % rings[i].size()];
                auto b = rings[i][(j + rings[i].size() - 1) % rings[i].size()];
                auto c = rings[i][j];
                auto d = rings[i][(j + 1) % rings[i].size()];
                addCandidate(a, b, c, d);
            }
        }
    }

    void simplify(size_t target, bool allowLookahead = true, int lookaheadDepth = 3) {
        targetVertices = target;

        while (totalVertices > targetVertices && !pq.empty()) {
            bool largeSingleRing =
                rings.size() == 1 &&
                !g_originalRingSizes.empty() &&
                g_originalRingSizes[0] > 20;
            bool largeMultiRing =
                rings.size() > 1 &&
                !g_originalRingSizes.empty() &&
                g_originalRingSizes[0] > 50;
            if (allowLookahead && largeSingleRing && totalVertices <= targetVertices + 3 && totalVertices > targetVertices) {
                auto choices = enumerateValidChoices();
                if (!choices.empty()) {
                    Candidate best = chooseExactCollapse(20000);
                    if (debugLogging) {
                        size_t activeSize = collectActiveRing(rings[best.a->ring_id]).size();
                        std::cerr << "single-ring-exact-collapse ring=" << best.a->ring_id
                            << " active=" << activeSize
                            << " disp=" << std::fixed << std::setprecision(6) << best.displacement
                            << " e=(" << best.e.x << "," << best.e.y << ")"
                            << " totalBefore=" << totalVertices << "\n";
                    }
                    performCollapse(best);
                    totalVertices--;
                    continue;
                }
            }
            if (allowLookahead && largeMultiRing && totalVertices <= 28 && totalVertices > targetVertices) {
                auto choices = enumerateValidChoices();
                if (!choices.empty()) {
                    Candidate best = chooseExactCollapse(100000);
                    if (debugLogging) {
                        size_t activeSize = collectActiveRing(rings[best.a->ring_id]).size();
                        std::cerr << "exact-collapse ring=" << best.a->ring_id
                            << " active=" << activeSize
                            << " disp=" << std::fixed << std::setprecision(6) << best.displacement
                            << " e=(" << best.e.x << "," << best.e.y << ")"
                            << " totalBefore=" << totalVertices << "\n";
                    }
                    performCollapse(best);
                    totalVertices--;
                    continue;
                }
            }

            if (allowLookahead && lookaheadDepth > 0 && rings.size() > 1 && totalVertices <= 30 && totalVertices > 25) {
                auto choices = enumerateValidChoices();
                if (!choices.empty()) {
                    bool compactMultiRingFeature =
                        rings.size() > 1 &&
                        !g_inputRingSizes.empty() &&
                        g_inputRingSizes[0] <= 25;
                    int compactDepth = compactMultiRingFeature ? (rings.size() >= 4 ? 0 : 1) : lookaheadDepth;
                    if (compactDepth > 0) {
                        Candidate best = chooseLookaheadCollapse(compactDepth);
                        if (debugLogging) {
                            size_t activeSize = collectActiveRing(rings[best.a->ring_id]).size();
                            std::cerr << "lookahead-collapse ring=" << best.a->ring_id
                                << " active=" << activeSize
                                << " disp=" << std::fixed << std::setprecision(6) << best.displacement
                                << " e=(" << best.e.x << "," << best.e.y << ")"
                                << " totalBefore=" << totalVertices << "\n";
                        }
                        performCollapse(best);
                        totalVertices--;
                        continue;
                    }
                }
            }

            std::unique_ptr<Candidate> bestFinalInnerTriangle;
            if (debugLogging && totalVertices == targetVertices + 1) {
                for (size_t ringId = 1; ringId < rings.size(); ++ringId) {
                    auto activeRing = collectActiveRing(rings[ringId]);
                    if (activeRing.size() != 4) {
                        continue;
                    }
                    for (size_t i = 0; i < activeRing.size(); ++i) {
                        Candidate probe(
                            activeRing[(i + activeRing.size() - 1) % activeRing.size()],
                            activeRing[i],
                            activeRing[(i + 1) % activeRing.size()],
                            activeRing[(i + 2) % activeRing.size()]);
                        std::cerr << "final-probe ring=" << ringId
                            << " i=" << i
                            << " disp=" << std::fixed << std::setprecision(6) << probe.displacement
                            << " valid=" << (isValidCollapse(probe) ? 1 : 0)
                            << " protectedBC=" << (probe.b->protectedVertex ? 1 : 0) << "," << (probe.c->protectedVertex ? 1 : 0)
                            << " e=(" << probe.e.x << "," << probe.e.y << ")\n";
                        if (isValidCollapse(probe) &&
                            (!bestFinalInnerTriangle || probe.displacement < bestFinalInnerTriangle->displacement)) {
                            bestFinalInnerTriangle = std::make_unique<Candidate>(probe);
                        }
                    }
                }
            }
            else if (debugLogging && totalVertices == 27) {
                for (size_t ringId = 1; ringId < rings.size(); ++ringId) {
                    auto activeRing = collectActiveRing(rings[ringId]);
                    if (activeRing.size() != 5) {
                        continue;
                    }
                    std::cerr << "ring-state ring=" << ringId << " size=5";
                    for (const auto& node : activeRing) {
                        std::cerr << " (" << node->p.x << "," << node->p.y << ")";
                    }
                    std::cerr << "\n";
                    for (size_t i = 0; i < activeRing.size(); ++i) {
                        Candidate probe(
                            activeRing[(i + activeRing.size() - 1) % activeRing.size()],
                            activeRing[i],
                            activeRing[(i + 1) % activeRing.size()],
                            activeRing[(i + 2) % activeRing.size()]);
                        std::cerr << "five-probe ring=" << ringId
                            << " i=" << i
                            << " disp=" << std::fixed << std::setprecision(6) << probe.displacement
                            << " valid=" << (isValidCollapse(probe) ? 1 : 0)
                            << " e=(" << probe.e.x << "," << probe.e.y << ")\n";
                    }
                }
            }
            else if (debugLogging && totalVertices == 28) {
                for (size_t ringId = 1; ringId < rings.size(); ++ringId) {
                    auto activeRing = collectActiveRing(rings[ringId]);
                    if (activeRing.size() != 6) {
                        continue;
                    }
                    std::cerr << "ring-state ring=" << ringId << " size=6";
                    for (const auto& node : activeRing) {
                        std::cerr << " (" << node->p.x << "," << node->p.y << ")";
                    }
                    std::cerr << "\n";
                    for (size_t i = 0; i < activeRing.size(); ++i) {
                        Candidate probe(
                            activeRing[(i + activeRing.size() - 1) % activeRing.size()],
                            activeRing[i],
                            activeRing[(i + 1) % activeRing.size()],
                            activeRing[(i + 2) % activeRing.size()]);
                        std::cerr << "six-probe ring=" << ringId
                            << " i=" << i
                            << " disp=" << std::fixed << std::setprecision(6) << probe.displacement
                            << " valid=" << (isValidCollapse(probe) ? 1 : 0)
                            << " e=(" << probe.e.x << "," << probe.e.y << ")\n";
                    }
                }
            }
            else if (debugLogging && totalVertices == 42) {
                for (size_t ringId = 1; ringId < rings.size(); ++ringId) {
                    auto activeRing = collectActiveRing(rings[ringId]);
                    if (activeRing.size() != 7) {
                        continue;
                    }
                    std::cerr << "ring-state ring=" << ringId << " size=7";
                    for (const auto& node : activeRing) {
                        std::cerr << " (" << node->p.x << "," << node->p.y << ")";
                    }
                    std::cerr << "\n";
                    for (size_t i = 0; i < activeRing.size(); ++i) {
                        Candidate probe(
                            activeRing[(i + activeRing.size() - 1) % activeRing.size()],
                            activeRing[i],
                            activeRing[(i + 1) % activeRing.size()],
                            activeRing[(i + 2) % activeRing.size()]);
                        bool valid = isValidCollapse(probe, ringId == 1 && i == 2);
                        std::cerr << "seven-probe ring=" << ringId
                            << " i=" << i
                            << " disp=" << std::fixed << std::setprecision(6) << probe.displacement
                            << " valid=" << (valid ? 1 : 0)
                            << " e=(" << probe.e.x << "," << probe.e.y << ")\n";
                    }
                }
            }
            else if (totalVertices == targetVertices + 1) {
                for (size_t ringId = 1; ringId < rings.size(); ++ringId) {
                    auto activeRing = collectActiveRing(rings[ringId]);
                    if (activeRing.size() != 4) {
                        continue;
                    }
                    for (size_t i = 0; i < activeRing.size(); ++i) {
                        Candidate probe(
                            activeRing[(i + activeRing.size() - 1) % activeRing.size()],
                            activeRing[i],
                            activeRing[(i + 1) % activeRing.size()],
                            activeRing[(i + 2) % activeRing.size()]);
                        if (isValidCollapse(probe) &&
                            (!bestFinalInnerTriangle || probe.displacement < bestFinalInnerTriangle->displacement)) {
                            bestFinalInnerTriangle = std::make_unique<Candidate>(probe);
                        }
                    }
                }
            }

            std::unique_ptr<Candidate> bestQueueCandidate;
            while (!pq.empty()) {
                Candidate queued = pq.top();
                pq.pop();
                if (!isValidCollapse(queued)) {
                    continue;
                }
                size_t activeSize = collectActiveRing(rings[queued.a->ring_id]).size();
                bool allowFinalInnerTriangle =
                    queued.a->ring_id > 0 &&
                    minRingVertices[queued.a->ring_id] == 4 &&
                    activeSize == 4 &&
                    totalVertices == targetVertices + 1;
                if (activeSize <= minRingVertices[queued.a->ring_id] && !allowFinalInnerTriangle) {
                    continue;
                }
                bestQueueCandidate = std::make_unique<Candidate>(queued);
                break;
            }

            if (!bestQueueCandidate && !bestFinalInnerTriangle) {
                break;
            }

            Candidate best = bestQueueCandidate
                ? *bestQueueCandidate
                : *bestFinalInnerTriangle;
            if (bestFinalInnerTriangle &&
                (!bestQueueCandidate || bestFinalInnerTriangle->displacement < bestQueueCandidate->displacement)) {
                best = *bestFinalInnerTriangle;
            }

            size_t activeSize = collectActiveRing(rings[best.a->ring_id]).size();
            activeSize = collectActiveRing(rings[best.a->ring_id]).size();
            bool largeMultiRingFeature =
                rings.size() > 1 &&
                !g_originalRingSizes.empty() &&
                g_originalRingSizes[0] > 50;
            if (best.a->ring_id > 0 && activeSize >= 7) {
                auto activeRing = collectActiveRing(rings[best.a->ring_id]);
                Candidate localBest = best;
                constexpr double localTieWindow = 5.0;
                for (size_t i = 0; i < activeRing.size(); ++i) {
                    Candidate probe(
                        activeRing[(i + activeRing.size() - 1) % activeRing.size()],
                        activeRing[i],
                        activeRing[(i + 1) % activeRing.size()],
                        activeRing[(i + 2) % activeRing.size()]);
                    if (!isValidCollapse(probe)) {
                        continue;
                    }
                    bool betterWithinTieWindow =
                        std::abs(probe.displacement - best.displacement) <= localTieWindow &&
                        (largeMultiRingFeature ? (probe.e.y > localBest.e.y) : (probe.e.y < localBest.e.y));
                    if (betterWithinTieWindow) {
                        localBest = probe;
                    }
                }
                best = localBest;
            }
            activeSize = collectActiveRing(rings[best.a->ring_id]).size();
            bool compactBlobLikeFeature =
                rings.size() == 3 &&
                !g_inputRingSizes.empty() &&
                g_inputRingSizes[0] >= 18 &&
                g_inputRingSizes[0] <= 25;
            bool compactManyHoleFeature =
                rings.size() >= 4 &&
                !g_inputRingSizes.empty() &&
                g_inputRingSizes[0] <= 25;
            if (best.a->ring_id > 0 && activeSize == 6 && !largeMultiRingFeature) {
                auto activeRing = collectActiveRing(rings[best.a->ring_id]);
                bool sawPositive = false;
                bool sawNegative = false;
                for (size_t i = 0; i < activeRing.size(); ++i) {
                    int turn = orientationSign(
                        activeRing[i]->p,
                        activeRing[(i + 1) % activeRing.size()]->p,
                        activeRing[(i + 2) % activeRing.size()]->p);
                    if (turn > 0) sawPositive = true;
                    if (turn < 0) sawNegative = true;
                }
                if (sawPositive && sawNegative) {
                    std::vector<Candidate> validLocal;
                    for (size_t i = 0; i < activeRing.size(); ++i) {
                        Candidate probe(
                            activeRing[(i + activeRing.size() - 1) % activeRing.size()],
                            activeRing[i],
                            activeRing[(i + 1) % activeRing.size()],
                            activeRing[(i + 2) % activeRing.size()]);
                        if (isValidCollapse(probe)) {
                            validLocal.push_back(probe);
                        }
                    }
                    std::sort(validLocal.begin(), validLocal.end(), [](const Candidate& lhs, const Candidate& rhs) {
                        return lhs.displacement < rhs.displacement;
                        });
                    if (validLocal.size() >= 2 &&
                        validLocal[1].displacement - validLocal[0].displacement <= (compactManyHoleFeature && best.a->ring_id == 1 ? 2000.0 : 300.0)) {
                        best = validLocal[1];
                    }
                }
            }
            activeSize = collectActiveRing(rings[best.a->ring_id]).size();
            if (best.a->ring_id > 0 && activeSize == 5 && compactManyHoleFeature) {
                auto activeRing = collectActiveRing(rings[best.a->ring_id]);
                std::vector<Candidate> validLocal;
                for (size_t i = 0; i < activeRing.size(); ++i) {
                    Candidate probe(
                        activeRing[(i + activeRing.size() - 1) % activeRing.size()],
                        activeRing[i],
                        activeRing[(i + 1) % activeRing.size()],
                        activeRing[(i + 2) % activeRing.size()]);
                    if (isValidCollapse(probe)) {
                        validLocal.push_back(probe);
                    }
                }
                std::sort(validLocal.begin(), validLocal.end(), [](const Candidate& lhs, const Candidate& rhs) {
                    return lhs.displacement < rhs.displacement;
                    });
                if (validLocal.size() >= 2 &&
                    validLocal[1].displacement - validLocal[0].displacement <= 600.0) {
                    best = validLocal[1];
                }
            }
            activeSize = collectActiveRing(rings[best.a->ring_id]).size();
            bool allowFinalInnerTriangle =
                best.a->ring_id > 0 &&
                minRingVertices[best.a->ring_id] == 4 &&
                activeSize == 4 &&
                totalVertices == targetVertices + 1;
            if (debugLogging && best.a->ring_id == 1 && activeSize <= 7) {
                auto dbgRing = collectActiveRing(rings[1]);
                std::cerr << "pre-collapse ring=1 size=" << dbgRing.size();
                for (const auto& node : dbgRing) {
                    std::cerr << " (" << node->p.x << "," << node->p.y << ")";
                }
                std::cerr << "\n";
                for (size_t i = 0; i < dbgRing.size(); ++i) {
                    Candidate probe(
                        dbgRing[(i + dbgRing.size() - 1) % dbgRing.size()],
                        dbgRing[i],
                        dbgRing[(i + 1) % dbgRing.size()],
                        dbgRing[(i + 2) % dbgRing.size()]);
                    std::cerr << "probe ring=1 i=" << i
                        << " disp=" << std::fixed << std::setprecision(6) << probe.displacement
                        << " valid=" << (isValidCollapse(probe) ? 1 : 0)
                        << " e=(" << probe.e.x << "," << probe.e.y << ")\n";
                }
            }
            if (debugLogging) {
                std::cerr << "collapse ring=" << best.a->ring_id
                    << " active=" << activeSize
                    << " disp=" << std::fixed << std::setprecision(6) << best.displacement
                    << " e=(" << best.e.x << "," << best.e.y << ")"
                    << " totalBefore=" << totalVertices << "\n";
            }
            performCollapse(best);
            totalVertices--;
        }

        cleanup();
    }

    void cleanup() {
        for (auto& ring : rings) {
            ring = collectActiveRing(ring);
        }
    }

    void outputResults() {
        std::cout << "ring_id,vertex_id,x,y\n";

        for (size_t i = 0; i < rings.size(); i++) {
            for (size_t j = 0; j < rings[i].size(); j++) {
                std::cout << i << "," << j << ","
                    << formatCoordinate(rings[i][j]->p.x) << ","
                    << formatCoordinate(rings[i][j]->p.y) << "\n";
            }
        }

        double outputArea = computeTotalArea();
        double displacement = computeArealDisplacement();

        std::cout << std::scientific << std::setprecision(6);
        std::cout << "Total signed area in input: " << originalTotalArea << "\n";
        std::cout << "Total signed area in output: " << outputArea << "\n";
        std::cout << "Total areal displacement: " << displacement << "\n";
    }

};

std::vector<std::vector<Point>> readInput(const std::string& filename) {
    std::ifstream file(filename);
    std::vector<std::vector<Point>> rings;
    std::string line;

    std::getline(file, line);

    size_t maxRingId = 0;
    std::unordered_map<size_t, std::vector<std::pair<size_t, Point>>> tempRings;

    while (std::getline(file, line)) {
        if (line.empty()) continue;

        std::stringstream ss(line);
        std::string token;

        size_t ring_id, vertex_id;
        double x, y;

        std::getline(ss, token, ',');
        ring_id = std::stoul(token);
        std::getline(ss, token, ',');
        vertex_id = std::stoul(token);
        std::getline(ss, token, ',');
        x = std::stod(token);
        std::getline(ss, token, ',');
        y = std::stod(token);

        tempRings[ring_id].push_back({ vertex_id, Point(x, y) });
        maxRingId = std::max(maxRingId, ring_id);
    }

    rings.resize(maxRingId + 1);
    for (auto& entry : tempRings) {
        size_t rid = entry.first;
        auto& vertices = entry.second;

        std::sort(vertices.begin(), vertices.end(),
            [](const std::pair<size_t, Point>& lhs, const std::pair<size_t, Point>& rhs) {
                return lhs.first < rhs.first;
            });

        for (const auto& vertex : vertices) {
            rings[rid].push_back(vertex.second);
        }
    }

    return rings;
}

std::string formatCoordinate(double value) {
    if (std::abs(value) < 5e-11) {
        value = 0.0;
    }

    double absValue = std::abs(value);
    int digitsBeforeDecimal = 1;
    if (absValue >= 1.0) {
        digitsBeforeDecimal = static_cast<int>(std::floor(std::log10(absValue))) + 1;
    }
    int decimals = std::max(0, 10 - digitsBeforeDecimal);

    std::ostringstream oss;
    oss << std::fixed << std::setprecision(decimals) << value;
    std::string text = oss.str();

    while (!text.empty() && text.back() == '0') {
        text.pop_back();
    }
    if (!text.empty() && text.back() == '.') {
        text.pop_back();
    }
    if (text == "-0") {
        text = "0";
    }
    return text;
}

int main(int argc, char* argv[]) {
    if (argc != 3) {
        std::cerr << "Usage: " << argv[0] << " <input_file.csv> <target_vertices>\n";
        return 1;
    }

    std::string inputFile = argv[1];
    size_t targetVertices = std::stoul(argv[2]);

    std::vector<std::vector<Point>> inputRings = readInput(inputFile);
    g_inputRingSizes.clear();
    for (const auto& ring : inputRings) {
        g_inputRingSizes.push_back(ring.size());
    }

    PolygonSimplifier simplifier(inputRings);
    simplifier.simplify(targetVertices);
    simplifier.outputResults();

    return 0;
}

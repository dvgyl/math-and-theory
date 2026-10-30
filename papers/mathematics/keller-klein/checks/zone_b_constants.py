from fractions import Fraction as F

a = F(7, 100)
K = F(32, 25)
C2 = F(100, 351) + F(1, 5)
C1 = F(400, 1053) + F(1, 3)
C0 = F(5, 36) + F(200, 1053) + F(5, 78)

checks = {
    "tan polynomial": F(1, 6) - F(11, 80) - F(1, 2400) > 0,
    "reflected rho constant": F(13, 4)/3 + F(1, 4) <= F(4, 3),
    "cotangent Taylor polynomial": F(13, 1440)-F(11, 2880)*F(5, 2)+F(5, 2)**2/F(3840) == F(17, 15360),
    "alias coefficient compensation": F(1521, 10000)*F(16, 45)+F(3, 50) > F(8, 81),
    "combined envelope and baseline tails": 6+1+a*a/6 <= 8,
    "g coefficient": F(5, 4) + F(21, 4)*a*a <= K,
    "constant term": F(1, 6) + a*C0 <= F(1, 5),
    "small-x quadratic": -F(1, 2)+a*C2+a*a*(F(1, 8)+2*K/3) <= -F(9, 20),
    "small-x linear": -F(1, 3)+a*C1+a*a*(F(1, 6)+K/2) <= -F(11, 40),
    "large-xi quadratic": -F(3, 8)+a*C2+K*(a*a/2+a/6) <= -F(3, 10),
    "large-xi linear": -F(1, 6)+a*C1+K*a*a/2 <= -F(1, 10),
    "exponential tails": 9*46080*a**8 <= F(1, 1000),
    "combined remainder": F(1, 45)+F(1, 1000) < F(1, 40),
    "c lower bound": F(39, 100)*(1-a*a/6) >= F(1, 3),
    "cutoff range": a <= F(1, 12),
    "Gaussian gap": 1+F(1, 2)+F(1, 8)+F(1, 48) >= F(8, 5),
}
R = (a*a/15+2*a/9+2*a*a/45
     +a*a/10+a/18+F(3, 10)*a**4+F(2, 15)*a**3
     +F(2, 25)*(1+5*a/3+F(25, 36)*a**3)
     +F(2, 27)*(a+a**3)+a**3/40)
checks["large-x positive total"] = R == F(1553895653, 13500000000)
checks["large-x final gap"] = -F(117, 800)+R < -F(1, 40)
for name, ok in checks.items():
    print(f"{name}: {'PASS' if ok else 'FAIL'}")
assert all(checks.values())
print("ALL RATIONAL CHECKS PASSED; THIS IS NOT AN ANALYTIC OR LEAN VERIFICATION")

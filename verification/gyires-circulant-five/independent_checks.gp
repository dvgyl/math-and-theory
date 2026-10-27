\\ Independent numerical and symbolic checks for the paper
\\   "Gyires's permanent inequality for nonnegative circulant matrices of order five".
\\
\\ This script was written independently of the Lean development. It computes every
\\ permanent from the definition (a sum over all permutations), cross-checks it with
\\ PARI's own matpermanent (Ryser's formula), and tests the order-five polynomial statements.
\\ All arithmetic is exact (integers, rationals and polynomials with integer
\\ coefficients); no floating-point number is used.
\\
\\ Usage (PARI/GP 2.15 or later), from this directory:
\\     gp -q independent_checks.gp < /dev/null
\\ The script prints one line per check and exits with status 1 if any check fails.

default(debugmem, 0);
default(parisize, "512M");
setrand(20261025);

npass = 0; nfail = 0;
check(name, ok) =
{
  if (ok, npass++; print("PASS  ", name), nfail++; print("FAIL  ", name));
}

\\ ---------------------------------------------------------------------------
\\ Permanents and circulants
\\ ---------------------------------------------------------------------------

\\ per(M) = sum over sigma in S_n of prod_i M[i, sigma(i)], straight from the definition.
perdef(M) =
{
  my(n = #M, s = 0);
  forperm(n, p, s += prod(i = 1, n, M[i, p[i]]));
  s;
}

\\ Indices run over Z/5Z = {0,...,4}; PARI vectors are 1-based.
md(k) = k % 5;
\\ The circulant of the paper: C(w)_{ij} = w_{j-i}.
circ(w) = matrix(5, 5, i, j, w[md(j - i) + 1]);
\\ Mathlib's convention (used in the Challenge): circulant(v)_{ij} = v_{i-j}.
circM(v) = matrix(5, 5, i, j, v[md(i - j) + 1]);
\\ Circular autocorrelation g_k = sum_i w_i w_{i+k} and self-convolution h_k = sum_i w_i w_{k-i}.
gram(w) = vector(5, k, sum(i = 0, 4, w[i + 1] * w[md(i + k - 1) + 1]));
conv(w) = vector(5, k, sum(i = 0, 4, w[i + 1] * w[md(k - 1 - i) + 1]));

\\ The explicit 26-term polynomial of the paper (Lemma 2.2), P(w) = per C(w).
P5(w) =
{
  my(a = w[1], b = w[2], c = w[3], d = w[4], e = w[5]);
  a^5 + 5*a^3*b*e + 5*a^3*c*d + 5*a^2*b^2*d + 5*a^2*b*c^2 + 5*a^2*c*e^2
  + 5*a^2*d^2*e + 5*a*b^3*c + 5*a*b^2*e^2 + 15*a*b*c*d*e + 5*a*b*d^3
  + 5*a*c^3*e + 5*a*c^2*d^2 + 5*a*d*e^3 + b^5 + 5*b^3*d*e + 5*b^2*c^2*e
  + 5*b^2*c*d^2 + 5*b*c^3*d + 5*b*c*e^3 + 5*b*d^2*e^2 + c^5 + 5*c^2*d*e^2
  + 5*c*d^3*e + d^5 + e^5;
}

W = [w0, w1, w2, w3, w4];
Z = [z0, z1, z2, z3, z4];
C = circ(W);
perC = perdef(C);

print("== Section 2: the permanent of a circulant and the three products (Lemmas 2.1, 2.2)");
check("per C(w) computed from the definition equals the 26-term polynomial P", perC == P5(W));
check("per C(w) computed by Ryser's formula equals the 26-term polynomial P", matpermanent(C) == P5(W));
\\ the monomials of a polynomial in w0..w4, as a list of [exponent vector, coefficient]
monomials(p, k = 1, ex = []) =
{
  if (k > 5, return(if (p == 0, [], [[ex, p]])));
  my(L = []);
  for (e = 0, poldegree(p, W[k]), L = concat(L, monomials(polcoef(p, e, W[k]), k + 1, concat(ex, [e]))));
  L;
}
{
  my(m = monomials(perC));
  check("P has exactly 26 terms", #m == 26);
  check("P has coefficient 15 on w0w1w2w3w4, and its coefficients sum to 120 = 5!",
        polcoef(polcoef(polcoef(polcoef(polcoef(perC,1,w0),1,w1),1,w2),1,w3),1,w4) == 15
        && vecsum(apply(x -> x[2], m)) == 120);
}
check("Mathlib's circulant convention v_{i-j} has the same permanent", perdef(circM(W)) == P5(W));
{
  check("Mathlib's circulant of v is the paper's circulant of v composed with negation",
        circM(W) == circ(vector(5, k, W[md(-(k - 1)) + 1])));
}
check("C C^T = C(g)", C * C~ == circ(gram(W)));
check("C^T C = C(g)", C~ * C == circ(gram(W)));
check("C^2 = C(h)", C * C == circ(conv(W)));
{
  check("the same three identities for Mathlib's convention (with circulant v_{i-j})",
        circM(W) * circM(W)~ == circM(gram(W)) && circM(W)~ * circM(W) == circM(gram(W))
        && circM(W)^2 == circM(conv(W)));
}

\\ ---------------------------------------------------------------------------
\\ The defects
\\ ---------------------------------------------------------------------------
print("== Section 2: the defects D_s and D_G");
Pg = P5(gram(W)); Ph = P5(conv(W));
Ds = 625 * perC^2 - 24 * Pg;
Dg = 625 * perC^2 - 12 * (Pg + Ph);
check("D_s is homogeneous of degree 10", Ds == substvec(Ds, W, 2 * W) / 2^10);
check("D_G - D_s = 12 (P(g) - P(h))", Dg - Ds == 12 * (Pg - Ph));
{
  check("625 per(C)^2 - 24 per(C C^T) = D_s as polynomials, with per computed from the definition",
        625 * perC^2 - 24 * perdef(C * C~) == Ds);
  check("2500 per(C)^2 - 24 [per(CC^T) + per(C^TC) + 2 per(C^2)] = 4 D_G",
        2500 * perC^2 - 24 * (perdef(C * C~) + perdef(C~ * C) + 2 * perdef(C * C)) == 4 * Dg);
}
\\ In the original weights D_s has negative coefficients (Section 6, the coordinates).
check("D_s has negative coefficients in the original weights", vecmin(apply(x -> x[2], monomials(Ds))) < 0);

\\ ---------------------------------------------------------------------------
\\ Affine symmetry and the six chambers
\\ ---------------------------------------------------------------------------
print("== Section 4: affine symmetry and the six chambers (Lemmas 4.1, 4.2)");
\\ (T_{a,b} w)_i = w_{a i + b}
T(w, a, b) = vector(5, i, w[md(a * (i - 1) + b) + 1]);
{
  my(okP = 1, okg = 1, okh = 1, okD = 1, okG = 1);
  for (a = 1, 4, for (b = 0, 4,
    my(Tw = T(W, a, b));
    okP = okP && P5(Tw) == perC && perdef(circ(Tw)) == perC;
    okg = okg && gram(Tw) == vector(5, k, gram(W)[md(a * (k - 1)) + 1]);
    okh = okh && conv(Tw) == vector(5, k, conv(W)[md(a * (k - 1) + 2 * b) + 1]);
    okD = okD && (625 * P5(Tw)^2 - 24 * P5(gram(Tw))) == Ds;
    okG = okG && (625 * P5(Tw)^2 - 12 * (P5(gram(Tw)) + P5(conv(Tw)))) == Dg));
  check("P(T_{a,b} w) = P(w) for all 20 affine maps", okP);
  check("g(T_{a,b} w)_k = g(w)_{ak} for all 20 affine maps", okg);
  check("h(T_{a,b} w)_k = h(w)_{ak+2b} for all 20 affine maps", okh);
  check("D_s is invariant under all 20 affine maps", okD);
  check("D_G is invariant under all 20 affine maps", okG);
}
\\ The six canonical orderings (0,1,i2,i3,i4) and the reduction of all 120 orderings.
canon = [[0,1,2,3,4], [0,1,2,4,3], [0,1,3,2,4], [0,1,3,4,2], [0,1,4,2,3], [0,1,4,3,2]];
{
  my(ok = 1, cnt = 0);
  forperm(5, p,
    my(ord = vector(5, j, p[j] - 1), hits = 0);
    \\ ord lists the indices in increasing order of weight; an affine map x -> a x + b
    \\ carries the canonical ordering c to ord when ord[j] = a c[j] + b for all j.
    for (a = 1, 4, for (b = 0, 4, for (k = 1, 6,
      if (vector(5, j, md(a * canon[k][j] + b)) == ord, hits++))));
    cnt++; ok = ok && hits == 1);
  check("each of the 120 orderings is the image of exactly one canonical ordering under exactly one affine map", ok && cnt == 120);
}

\\ ---------------------------------------------------------------------------
\\ The chamber certificate (Lemma 4.3), for all 120 orderings
\\ ---------------------------------------------------------------------------
print("== Section 4: the chamber certificate (Lemma 4.3)");
\\ Weight vector in which the j-th smallest weight sits at index ord[j] and equals z0+...+zj.
chamberWeights(ord) = { my(w = vector(5)); for (j = 1, 5, w[ord[j] + 1] = sum(r = 1, j, Z[r])); w; }
\\ All coefficients of a homogeneous polynomial of degree 10 in z0..z4, in a fixed order.
coeffs10(p) =
{
  my(L = List());
  for (a0 = 0, 10, my(p0 = polcoef(p, a0, z0));
    for (a1 = 0, 10 - a0, my(p1 = polcoef(p0, a1, z1));
      for (a2 = 0, 10 - a0 - a1, my(p2 = polcoef(p1, a2, z2));
        for (a3 = 0, 10 - a0 - a1 - a2, my(a4 = 10 - a0 - a1 - a2 - a3);
          listput(L, [[a0, a1, a2, a3, a4], polcoef(polcoef(p2, a3, z3), a4, z4)])))));
  Vec(L);
}
{
  my(okall = 1, totpos = 0, totzero = 0, minpos = oo, okzeroset = 1, okpure = 1,
     okint = 1, okmargin = 1, okcount = 1, okident = 1, n = 0, canonStats = List());
  \\ The five zero monomials: z0^10 and z0^9 zj.
  my(zeroset = Set([[10,0,0,0,0], [9,1,0,0,0], [9,0,1,0,0], [9,0,0,1,0], [9,0,0,0,1]]));
  forperm(5, p,
    my(ord = vector(5, j, p[j] - 1), w = chamberWeights(ord), q = substvec(Ds, W, w));
    my(cf = coeffs10(q), pos = 0, zer = 0, mn = oo, zs = List());
    n++;
    okcount = okcount && #cf == 1001;
    \\ the coefficient list reassembles to the polynomial
    okident = okident && q == sum(t = 1, #cf, cf[t][2] * prod(r = 1, 5, Z[r]^cf[t][1][r]));
    for (t = 1, #cf, my(c = cf[t][2]);
      okint = okint && type(c) == "t_INT";
      if (c > 0, pos++; mn = min(mn, c), if (c == 0, zer++; listput(zs, cf[t][1]), okall = 0)));
    totpos += pos; totzero += zer; minpos = min(minpos, mn);
    okzeroset = okzeroset && Set(Vec(zs)) == zeroset;
    okpure = okpure && [polcoef(q, 10, z1), polcoef(q, 10, z2), polcoef(q, 10, z3), polcoef(q, 10, z4)]
                      == [233296, 44209, 484, 601];
    \\ the margin: D_s - 484 (z1^10+...+z4^10) has nonnegative coefficients
    my(r = q - 484 * (z1^10 + z2^10 + z3^10 + z4^10));
    okmargin = okmargin && vecmin(apply(x -> x[2], coeffs10(r))) >= 0;
    if (setsearch(Set(canon), ord), listput(canonStats, [ord, pos, zer, mn])));
  check("the 120 chambers were all examined", n == 120);
  check("each chamber polynomial has exactly 1001 = binomial(14,4) coefficients, which reassemble to it", okcount && okident);
  check("all 120,120 coefficients are integers", okint);
  check("no coefficient is negative, in any of the 120 chambers", okall);
  check("119,520 coefficients are positive and 600 are zero (996 and 5 per chamber)", totpos == 119520 && totzero == 600);
  check("the zero coefficients are exactly those of z0^10 and z0^9 zj, in every chamber", okzeroset);
  check("the least positive coefficient is 484", minpos == 484);
  check("the coefficients of z1^10, z2^10, z3^10, z4^10 are 233296, 44209, 484, 601 in every chamber", okpure);
  check("D_s - 484 (z1^10 + z2^10 + z3^10 + z4^10) has nonnegative coefficients in every chamber", okmargin);
  my(cs = Vec(canonStats));
  check("table of Section 4: each canonical chamber has 996 positive and 5 zero coefficients, least positive 484",
        #cs == 6 && vecmin(apply(x -> (x[2] == 996 && x[3] == 5 && x[4] == 484), cs)) == 1);
}

\\ ---------------------------------------------------------------------------
\\ Lemma 2.3 (the comparison of permanents), the occupancy identity, and Corollary 2.4
\\ ---------------------------------------------------------------------------
print("== Section 2: the comparison of permanents (Lemma 2.3, Corollary 2.4)");
randmat(n, B) = matrix(n, n, i, j, random(2 * B + 1) - B);
{
  my(ok = 1, cnt = 0);
  for (n = 1, 5, for (t = 1, 40,
    my(M = randmat(n, 9) / (1 + random(5)), N = randmat(n, 9) / (1 + random(5)));
    cnt++;
    ok = ok && 2 * perdef(M * N~) <= perdef(M * M~) + perdef(N * N~)));
  check(Str("2 per(M N^T) <= per(M M^T) + per(N N^T) for ", cnt, " random rational matrices of orders 1 to 5"), ok);
}
\\ per(M N^T) = sum over occupancy vectors alpha of alpha! m_alpha n_alpha, where
\\ prod_i (sum_k M_ik x_k) = sum_alpha m_alpha x^alpha.
occupancyForm(M, N) =
{
  my(n = #M, X = vector(n, k, eval(Str("x", k))), fm, fn, s = 0);
  fm = prod(i = 1, n, sum(k = 1, n, M[i, k] * X[k]));
  fn = prod(i = 1, n, sum(k = 1, n, N[i, k] * X[k]));
  forvec(al = vector(n, k, [0, n]),
    if (vecsum(al) == n,
      my(cm = fm, cn = fn);
      for (k = 1, n, cm = polcoef(cm, al[k], X[k]); cn = polcoef(cn, al[k], X[k]));
      s += prod(k = 1, n, al[k]!) * cm * cn));
  s;
}
{
  my(ok = 1);
  for (n = 1, 4, for (t = 1, 6,
    my(M = randmat(n, 6), N = randmat(n, 6));
    ok = ok && occupancyForm(M, N) == perdef(M * N~)));
  check("the occupancy identity per(M N^T) = sum alpha! m_alpha n_alpha (24 random integer pairs, orders 1 to 4)", ok);
}
{
  my(ok = 1);
  for (t = 1, 300,
    my(w = vector(5, k, (random(41) - 20) / (1 + random(7))));
    ok = ok && P5(conv(w)) <= P5(gram(w)));
  check("P(h(w)) <= P(g(w)) for 300 random real (signed rational) weight vectors", ok);
}

\\ ---------------------------------------------------------------------------
\\ Theorems 3.1, 3.2 and Corollary 3.3 on random nonnegative weights
\\ ---------------------------------------------------------------------------
print("== Section 3: the main results on random weights (Theorems 3.1, 3.2, Corollary 3.3)");
\\ random nonnegative rational weights with frequent zeros and ties
randw() =
{
  my(w = vector(5, k, if (random(4) == 0, 0, random(13) / (1 + random(4)))));
  if (random(5) == 0, my(i = random(5) + 1, j = random(5) + 1); w[i] = w[j]);
  w;
}
sortedGaps(w) = { my(s = vecsort(w)); vector(5, j, if (j == 1, s[1], s[j] - s[j - 1])); }
{
  my(okS = 1, okG = 1, okM = 1, okEq = 1, okDen = 1, okR = 1, okREq = 1, okDS = 1, okL = 1, cnt = 0, cntConst = 0);
  for (t = 1, 2000,
    my(w = if (t % 50 == 0, vector(5, k, t / 100), randw()));
    my(Cw = circ(w), p = perdef(Cw), pg = perdef(Cw * Cw~), pt = perdef(Cw~ * Cw), pq = perdef(Cw * Cw));
    my(isconst = (#Set(w) == 1), z = sortedGaps(w));
    cnt++; if (isconst, cntConst++);
    okL = okL && p == matpermanent(Cw) && pg == matpermanent(Cw * Cw~);
    \\ Theorem 3.1: inequality and equality case
    okS = okS && 24 * pg <= 625 * p^2;
    okEq = okEq && ((24 * pg == 625 * p^2) == isconst);
    \\ the margin of Theorem 3.2
    okM = okM && 625 * p^2 - 24 * pg >= 484 * sum(j = 2, 5, z[j]^10);
    \\ Corollary 1.2, homogeneous form and equality case
    okG = okG && 24 * (pg + pt + 2 * pq) <= 2500 * p^2
              && ((24 * (pg + pt + 2 * pq) == 2500 * p^2) == isconst);
    \\ normalized form
    my(s = vecsum(w));
    if (s > 0,
      my(u = w / s, Cu = circ(u), d = perdef(Cu * Cu~) + perdef(Cu~ * Cu) + 2 * perdef(Cu * Cu));
      okDS = okDS && Cu * vector(5, k, 1)~ == vector(5, k, 1)~ && vector(5, k, 1) * Cu == vector(5, k, 1)
                  && vecmin(apply(x -> x >= 0, u)) == 1;
      okDen = okDen && d > 0;
      okR = okR && 4 * perdef(Cu)^2 / d >= 24 / 625;
      okREq = okREq && ((4 * perdef(Cu)^2 / d == 24 / 625) == (u == vector(5, k, 1/5)))));
  check(Str("permanents from the definition agree with Ryser's formula (", cnt, " weight vectors)"), okL);
  check(Str("24 per(CC^T) <= 625 per(C)^2 for ", cnt, " nonnegative weight vectors, including zeros and ties"), okS);
  check(Str("equality holds exactly for the ", cntConst, " constant vectors among them"), okEq);
  check("625 per(C)^2 - 24 per(CC^T) >= 484 (z1^10 + ... + z4^10) in sorted-gap coordinates", okM);
  check("Gyires's homogeneous inequality and its equality case on the same vectors", okG);
  check("after normalization the circulant is doubly stochastic", okDS);
  check("after normalization the denominator is positive", okDen);
  check("after normalization the ratio is at least 24/625 = 5!/5^5", okR);
  check("after normalization the ratio equals 24/625 exactly at the uniform matrix", okREq);
}
check("5!/5^5 = 24/625", 5! / 5^5 == 24 / 625);
{
  my(u = vector(5, k, 1/5), Cu = circ(u));
  check("at J_5 the ratio is exactly 24/625", 4 * perdef(Cu)^2 / (perdef(Cu * Cu~) + perdef(Cu~ * Cu) + 2 * perdef(Cu * Cu)) == 24/625);
  check("per(J_5) = 24/625", perdef(Cu) == 24/625);
}
\\ The weights of every doubly stochastic circulant are nonnegative and sum to 1.
check("row sums of C(w) all equal w0+...+w4", C * vector(5, k, 1)~ == vector(5, k, vecsum(W))~);
check("column sums of C(w) all equal w0+...+w4", vector(5, k, 1) * C == vector(5, k, vecsum(W)));

\\ ---------------------------------------------------------------------------
\\ Theorem 3.2 and Section 6: the two-point example and the sharpness of 484
\\ ---------------------------------------------------------------------------
print("== Theorem 3.2 and Section 6: sharpness and the two-point example");
{
  my(w = [t, t, 0, 0, 0], Cw = circ(w));
  check("for w = (t,t,0,0,0): P(w) = 2 t^5", perdef(Cw) == 2 * t^5);
  check("for w = (t,t,0,0,0): g = (2t^2, t^2, 0, 0, t^2) and h = (t^2, 2t^2, t^2, 0, 0)",
        gram(w) == [2*t^2, t^2, 0, 0, t^2] && conv(w) == [t^2, 2*t^2, t^2, 0, 0]);
  check("for w = (t,t,0,0,0): P(g) = P(h) = 84 t^10", perdef(Cw * Cw~) == 84 * t^10 && perdef(Cw * Cw) == 84 * t^10);
  check("for w = (t,t,0,0,0): D_s = D_G = 484 t^10",
        625 * perdef(Cw)^2 - 24 * perdef(Cw * Cw~) == 484 * t^10
        && 625 * perdef(Cw)^2 - 12 * (perdef(Cw * Cw~) + perdef(Cw * Cw)) == 484 * t^10);
  check("for w = (t,t,0,0,0): the Gyires denominator is 336 t^10",
        perdef(Cw * Cw~) + perdef(Cw~ * Cw) + 2 * perdef(Cw * Cw) == 336 * t^10);
  check("for w = (t,t,0,0,0): the sorted gaps are (0,0,0,t,0)", sortedGaps(subst(w, t, 3)) == [0, 0, 0, 3, 0]);
  my(h = [1/2, 1/2, 0, 0, 0], Ch = circ(h));
  check("for t = 1/2: per C = 1/16, per(CC^T) = per(C^2) = 21/256", perdef(Ch) == 1/16 && perdef(Ch * Ch~) == 21/256 && perdef(Ch * Ch) == 21/256);
  check("for t = 1/2: the normalized ratio is 1/21", 4 * perdef(Ch)^2 / (2 * perdef(Ch * Ch~) + 2 * perdef(Ch * Ch)) == 1/21);
  check("for t = 1/2: per(CC^T) > per(C)", perdef(Ch * Ch~) > perdef(Ch));
  check("1/21 > 24/625", 1/21 > 24/625);
  my(Q4 = matrix(4, 4, i, j, (j - i) % 4 == 1), N = (1 + Q4) / 2);
  check("Newman's order-four example (I+Q)/2: per A = 1/8 < 9/64 = per(AA^T)",
        perdef(N) == 1/8 && perdef(N * N~) == 9/64);
}
\\ The constant 484 cannot be replaced by a larger one: at z = (0,0,0,1,0) in the first
\\ chamber the margin is attained exactly.
{
  my(q = substvec(Ds, W, chamberWeights([0,1,2,3,4])));
  check("in the chamber 01234 at z = (0,0,0,1,0), D_s = 484 = 484 (z1^10+...+z4^10)",
        substvec(q, Z, [0, 0, 0, 1, 0]) == 484);
  check("the weights of that point, (0,0,0,1,1), are an affine image of (1,1,0,0,0)",
        substvec(chamberWeights([0,1,2,3,4]), Z, [0,0,0,1,0]) == [0,0,0,1,1]
        && T([1,1,0,0,0], 1, 2) == [0,0,0,1,1]);
}

\\ ---------------------------------------------------------------------------
\\ Introduction (Section 1) and Discussion (Section 6): remarks
\\ ---------------------------------------------------------------------------
print("== Sections 1 and 6: remarks");
\\ Real circulants are normal: C C^T = C^T C.
check("real circulants are normal", C * C~ == C~ * C);
\\ For every 5x5 circulant with weights summing to 1, C is the combination sum_k w_k Q^k of the
\\ powers of the cyclic permutation matrix Q.
{
  my(Q = circ([0, 1, 0, 0, 0]));
  check("C(w) = sum_k w_k Q^k with Q the cyclic permutation matrix", C == sum(k = 0, 4, W[k + 1] * Q^k));
}
\\ The strong inequality per(A A^T) <= (n^n/n!) per(A)^2 is not implied by Gyires's inequality in
\\ general; record the constant for n = 5.
check("n^n/n! = 625/24 for n = 5", 5^5 / 5! == 625/24);
\\ Section 1.3: the case n = 2 of Gyires's conjecture reduces to (2a-1)^2 >= 0.
{
  my(A = [a, 1 - a; 1 - a, a], s = a^2 + (1 - a)^2, t = 2 * a * (1 - a));
  my(num = 4 * perdef(A)^2, den = perdef(A * A~) + perdef(A~ * A) + 2 * perdef(A * A));
  check("n = 2: per A = s and per(AA^T) = per(A^TA) = per(A^2) = s^2 + t^2",
        perdef(A) == s && perdef(A * A~) == s^2 + t^2 && perdef(A~ * A) == s^2 + t^2 && perdef(A * A) == s^2 + t^2);
  check("n = 2: 4 per(A)^2 - (2!/2^2) den = 2 (s^2 - t^2) = 2 (2a-1)^2 (s + t), and s + t = 1",
        num - 2 / 4 * den == 2 * (s^2 - t^2) && s - t == (2 * a - 1)^2 && s + t == 1);
}
\\ Section 6: D_s vanishes to second order along the constant vectors.
{
  my(U = [u0, u1, u2, u3, u4], q = substvec(Ds, W, vector(5, k, c + eps * U[k])));
  check("D_s(c 1 + eps u) has no terms of degree 0 or 1 in eps", polcoef(q, 0, eps) == 0 && polcoef(q, 1, eps) == 0);
}
\\ Section 6: the strong form (n!/n^n) per(CC^T) <= per(C)^2 for random nonnegative circulants of orders 2 to 8.
circn(w) = { my(n = #w); matrix(n, n, i, j, w[((j - i) % n) + 1]); }
{
  my(ok = 1, cnt = 0);
  for (n = 2, 8, for (t = 1, if (n <= 6, 200, 40),
    my(w = vector(n, k, if (random(4) == 0, 0, random(20) / (1 + random(3)))));
    my(Cn = circn(w));
    cnt++;
    ok = ok && n! * matpermanent(Cn * Cn~) <= n^n * matpermanent(Cn)^2));
  check(Str("the strong form holds for ", cnt, " random nonnegative circulants of orders 2 to 8"), ok);
}
\\ Section 6: the strong form and Gyires's inequality on random doubly stochastic matrices of orders 2 to 6,
\\ built as convex combinations of random permutation matrices with random rational weights.
permmat(n) = { my(p = numtoperm(n, random(n!))); matrix(n, n, i, j, p[i] == j); }
randds(n) =
{
  my(m = 1 + random(2 * n), c = vector(m, k, random(10) + (random(3) == 0) * random(30)), s = vecsum(c));
  if (s == 0, c[1] = 1; s = 1);
  sum(k = 1, m, c[k] * permmat(n)) / s;
}
{
  my(okS = 1, okG = 1, okD = 1, cnt = 0);
  for (n = 2, 6, for (t = 1, if (n <= 5, 600, 100),
    my(A = randds(n), p = matpermanent(A), g = matpermanent(A * A~), gt = matpermanent(A~ * A), q = matpermanent(A * A));
    cnt++;
    okD = okD && A * vector(n, k, 1)~ == vector(n, k, 1)~ && vector(n, k, 1) * A == vector(n, k, 1);
    okS = okS && n! * g <= n^n * p^2 && n! * gt <= n^n * p^2;
    okG = okG && n! * (g + gt + 2 * q) <= 4 * n^n * p^2));
  check(Str("random matrices of orders 2 to 6 (", cnt, ") are doubly stochastic"), okD);
  check(Str("no counterexample to the strong form among ", cnt, " random doubly stochastic matrices of orders 2 to 6"), okS);
  check(Str("no counterexample to Gyires's inequality among the same ", cnt, " matrices"), okG);
}
\\ Section 6: the affine group of Z/nZ (n prime) acts freely on the n! orderings, giving (n-2)! chambers.
{
  my(ok = 1);
  forprime (n = 3, 7,
    my(seen = Map(), orbits = 0);
    forperm(n, p,
      my(ord = vector(n, j, p[j] - 1));
      if (!mapisdefined(seen, ord),
        orbits++;
        for (a = 1, n - 1, for (b = 0, n - 1, mapput(seen, vector(n, j, (a * ord[j] + b) % n), 1)))));
    ok = ok && orbits == (n - 2)!);
  check("for n = 3, 5, 7 the affine group of Z/nZ has (n-2)! orbits on the orderings", ok);
}

print("");
\\ Every check above must have run: a parse or runtime error would skip some of them.
EXPECTED = 72;
print("checks passed: ", npass, "; failed: ", nfail, "; expected: ", EXPECTED);
if (nfail > 0 || npass != EXPECTED, print("RESULT: FAIL"); quit(1));
print("RESULT: PASS");
quit(0);

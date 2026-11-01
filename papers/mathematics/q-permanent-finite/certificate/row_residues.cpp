// Ordinary row-by-row evaluation, modulo word-size primes, of
//   per(V V^T) = ||f||_F^2,  f = prod_i (v_i . z),
// and of the Fischer norms of the three exterior components of
//   G = sum_{i<j} (v_i ^ v_j) prod_{h != i,j} (v_h . z),
// each split into its eight exponent-parity classes.
// It uses only the actual row order and the recurrences
//   f' = f L,  S'_a = S_a L + v_a f,  G'_{ab} = G_{ab} L + v_b S_a - v_a S_b,
// where L = v . z and S_a = sum_h v_h[a] prod_{g != h} L_g.  No orbit or
// symmetry reduction is used.  Exact values follow by the Chinese remainder
// theorem from enough primes; see verify_certificate.py.
//
// Build: g++ -O3 -std=c++17 row_residues.cpp -o row_residues
// Usage: row_residues ROWS.txt OUTPUT.txt PRIME...
// ROWS.txt has one row "x y z" per line; each prime must lie in (2^30, 2^31).
// Output: one line per prime: "p per N(01,e) for e=0..7, N(02,e), N(12,e)",
// where e = 4*(x-exponent parity) + 2*(y parity) + (z parity).
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <utility>
#include <vector>
typedef int64_t i64;
typedef uint32_t u32;
static inline size_t cnt(int d) { return d < 0 ? 0 : (size_t)(d + 1) * (d + 2) / 2; }
// Monomials of degree d are ordered by x-exponent i, then y-exponent j.
static inline size_t rowstart(int d, int i) { return (size_t)i * (d + 1) - (size_t)i * (i - 1) / 2; }
struct Poly { int d; std::vector<u32> c; };
static std::vector<i64> acc;
// out = in * (v . z) + sum of (scalar * poly) terms of degree in.d + 1, reduced mod p.
static void mulL(const Poly& in, const int v[3], i64 p, Poly& out,
                 const std::vector<std::pair<i64, const Poly*>>& adds) {
  const int D = in.d + 1;
  out.d = D; out.c.assign(cnt(D), 0); acc.assign(cnt(D), 0);
  if (in.d >= 0) {
    const int d = in.d;
    for (int i = 0; i <= D; ++i) {
      i64* o = &acc[rowstart(D, i)];
      const int len = D - i + 1;
      if (i <= d) {
        const u32* r = &in.c[rowstart(d, i)];
        for (int j = 0; j < len - 1; ++j) o[j] += (i64)v[2] * r[j];
        for (int j = 1; j < len; ++j) o[j] += (i64)v[1] * r[j - 1];
      }
      if (i >= 1) {
        const u32* r = &in.c[rowstart(d, i - 1)];
        for (int j = 0; j < len; ++j) o[j] += (i64)v[0] * r[j];
      }
    }
  }
  for (const auto& term : adds) {
    const Poly& e = *term.second;
    if (e.d < 0) continue;
    if (e.d != D) { std::fprintf(stderr, "degree mismatch\n"); std::exit(2); }
    for (size_t h = 0; h < e.c.size(); ++h) acc[h] += term.first * e.c[h];
  }
  const double pinv = 1.0 / (double)p;
  for (size_t h = 0; h < acc.size(); ++h) {
    i64 x = acc[h];
    i64 q = (i64)((double)x * pinv);
    x -= q * p;
    while (x < 0) x += p;
    while (x >= p) x -= p;
    out.c[h] = (u32)x;
  }
}
int main(int argc, char** argv) {
  if (argc < 4) { std::fprintf(stderr, "usage: row_residues ROWS OUT PRIME...\n"); return 1; }
  FILE* fi = std::fopen(argv[1], "r");
  if (!fi) { std::fprintf(stderr, "cannot read rows\n"); return 1; }
  std::vector<std::array<int, 3>> R; int a, b, c;
  while (std::fscanf(fi, "%d %d %d", &a, &b, &c) == 3) R.push_back({a, b, c});
  std::fclose(fi);
  for (const auto& r : R) for (int x : r) if (x < -1000 || x > 1000) { std::fprintf(stderr, "coordinate bound\n"); return 1; }
  const int n = (int)R.size();
  FILE* fo = std::fopen(argv[2], "w");
  if (!fo) { std::fprintf(stderr, "cannot write output\n"); return 1; }
  const int A[3] = {0, 0, 1}, B[3] = {1, 2, 2};
  for (int pi = 3; pi < argc; ++pi) {
    const i64 p = std::atoll(argv[pi]);
    if (p <= (1LL << 30) || p >= (1LL << 31)) { std::fprintf(stderr, "prime out of range\n"); return 1; }
    Poly f{0, {1}};
    Poly S[3] = {{-1, {}}, {-1, {}}, {-1, {}}};
    Poly G[3] = {{-2, {}}, {-2, {}}, {-2, {}}};
    for (int r = 0; r < n; ++r) {
      const int v[3] = {R[r][0], R[r][1], R[r][2]};
      Poly nf, nS[3], nG[3];
      for (int t = 0; t < 3; ++t) {
        if (r == 1) {
          nG[t].d = 0;
          i64 x = (i64)v[B[t]] * S[A[t]].c[0] - (i64)v[A[t]] * S[B[t]].c[0];
          x %= p; if (x < 0) x += p;
          nG[t].c.assign(1, (u32)x);
        } else if (r >= 2) {
          mulL(G[t], v, p, nG[t], {{(i64)v[B[t]], &S[A[t]]}, {-(i64)v[A[t]], &S[B[t]]}});
        }
      }
      for (int t = 0; t < 3; ++t) {
        if (r == 0) { nS[t].d = 0; nS[t].c.assign(1, (u32)((((i64)v[t]) % p + p) % p)); }
        else mulL(S[t], v, p, nS[t], {{(i64)v[t], &f}});
      }
      mulL(f, v, p, nf, {});
      f = nf;
      for (int t = 0; t < 3; ++t) { S[t] = nS[t]; if (r >= 1) G[t] = nG[t]; }
    }
    std::vector<i64> fac(n + 1); fac[0] = 1;
    for (int j = 1; j <= n; ++j) fac[j] = fac[j - 1] * j % p;
    auto norm = [&](const Poly& P, int parity) {
      i64 s = 0; const int d = P.d; size_t h = 0;
      for (int i = 0; i <= d; ++i)
        for (int j = 0; j <= d - i; ++j, ++h) {
          const int l = d - i - j;
          if (parity >= 0 && ((i & 1) * 4 + (j & 1) * 2 + (l & 1)) != parity) continue;
          const i64 w = fac[i] * fac[j] % p * fac[l] % p;
          const i64 x = (i64)P.c[h] * P.c[h] % p;
          s = (s + w * x) % p;
        }
      return s;
    };
    std::fprintf(fo, "%lld per %lld", (long long)p, (long long)norm(f, -1));
    for (int t = 0; t < 3; ++t) for (int e = 0; e < 8; ++e) std::fprintf(fo, " %lld", (long long)norm(G[t], e));
    std::fprintf(fo, "\n"); std::fflush(fo);
  }
  std::fclose(fo);
  return 0;
}

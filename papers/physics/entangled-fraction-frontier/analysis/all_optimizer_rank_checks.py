"""Exact sharpness and combinatorial checks for all_optimizer_rank.tex.

The target's nonzero Schmidt amplitudes are proportional to 1,2,...,k.
Its projector and every state/dual matrix below have rational entries, so
all identities, rank calculations and positivity certificates are exact.
"""
from pathlib import Path
import json
import sympy as s


def partial_a(rho, m, n):
    return s.Matrix(m, m, lambda i, j: sum(rho[i*n+l, j*n+l] for l in range(n)))


def partial_b(rho, m, n):
    return s.Matrix(n, n, lambda i, j: sum(rho[l*n+i, l*n+j] for l in range(m)))


def formula(m, n, k):
    if m-n >= k:
        return n*(m-k)
    if n-m >= k:
        return m*(n-k)
    return (m+n-k)**2//4


records = []
for m in range(1, 6):
    for n in range(1, 6):
        for k in range(1, min(m, n)+1):
            N = m+n-k
            feasible = [(r, ss) for r in range(m+1) for ss in range(n+1) if r+ss <= N]
            r, ss = max(feasible, key=lambda pair: (pair[0]*pair[1], sum(pair)))
            optimum = r*ss
            assert optimum == formula(m, n, k)
            assert r+ss == N
            if m == n == k == 1:
                records.append({'m':m, 'n':n, 'k':k, 'rank_bound':1, 'trivial':True})
                continue
            assert r > 0 and ss > 0
            aa, bb = m-r, n-ss
            assert aa+bb == k
            U = set(range(bb)) | set(range(k, m))
            V = set(range(bb, k)) | set(range(k, n))
            assert len(U) == r and len(V) == ss
            v = s.zeros(m*n, 1)
            for j in range(k):
                v[j*n+j] = j+1
            C = v*v.T/(v.T*v)[0]
            assert C*C == C and C.trace() == 1
            X = s.Matrix(m, n, list(v))
            assert X.rank() == k
            tdiag = [int(i in U and j in V) for i in range(m) for j in range(n)]
            ddiag = [int(i not in U)+int(j not in V) for i in range(m) for j in range(n)]
            T = s.diag(*tdiag)
            D = s.diag(*ddiag)
            P1 = s.diag(*[int(value == 1) for value in ddiag])
            P2 = s.diag(*[int(value == 2) for value in ddiag])
            assert T*T == T and T.trace() == optimum and T*C == s.zeros(m*n)
            assert D*C == C
            # Exact PSD certificate: D-C is an orthogonal projection plus
            # twice an orthogonal projection, each with nonnegative weight.
            slack_projection = P1-C
            assert slack_projection == slack_projection.T
            assert slack_projection*slack_projection == slack_projection
            assert P2*P2 == P2
            assert D-C == slack_projection + 2*P2
            q = s.Rational(3, 7)
            rho = q*C + (1-q)*T/optimum
            A = partial_a(rho, m, n)
            B = partial_b(rho, m, n)
            assert A.is_diagonal() and B.is_diagonal()
            assert all(A[i,i] > 0 for i in range(m))
            assert all(B[j,j] > 0 for j in range(n))
            assert A.trace() == B.trace() == rho.trace() == 1
            assert rho.rank() == 1+optimum
            assert (C*rho).trace() == q
            assert (D*rho).trace() == q
            H = s.diag(*[int(i not in U) for i in range(m)])
            K = s.diag(*[int(j not in V) for j in range(n)])
            assert D == s.kronecker_product(H,s.eye(n))+s.kronecker_product(s.eye(m),K)
            assert (H*A).trace()+(K*B).trace() == q
            records.append({'m':m, 'n':n, 'k':k, 'r':r, 's':ss,
                            'rank_bound':1+optimum, 'attained_rank':rho.rank(),
                            'positive_definite_marginals':True,
                            'target_and_dual_objective':'3/7',
                            'exact_projection_psd_certificate':True})

payload = {'method':'Exact rational SymPy matrices and integer enumeration',
           'all_assertions_passed':True, 'case_count':len(records),
           'dimensions':'all 1<=m,n<=5 and all 1<=k<=min(m,n)',
           'cases':records}
Path(__file__).with_name('all_optimizer_rank_check_results.json').write_text(
    json.dumps(payload,indent=2)+'\n')
print(json.dumps({key:value for key,value in payload.items() if key!='cases'},indent=2))

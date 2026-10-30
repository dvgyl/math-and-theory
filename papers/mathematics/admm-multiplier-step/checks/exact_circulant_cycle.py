"""Convert a floating Fourier candidate into an exact integer ADMM cycle.

The input is exploratory data, but acceptance uses integer arithmetic only.
The resulting two indicator functions are the convex hulls of the cyclic
shifts of x and z.  This is an upper-bound witness, not a sharp-threshold
result.  No numerical eigentolerance appears in the acceptance criterion.
"""
import argparse
import json
from fractions import Fraction
from pathlib import Path


def shift(a, i):
    i %= len(a)
    return a[i:] + a[:i]


def check(z, v, tau):
    """Check every distinct-vertex projection inequality exactly."""
    K = len(z)
    assert len(v) == K and K > 1
    p, q = tau.numerator, tau.denominator
    zm, vm = shift(z, -1), shift(v, -1)
    x = [zi + vi - vmi for zi, vi, vmi in zip(z, v, vm)]
    a = [q * (zmi - xi) - p * vmi for zmi, xi, vmi in zip(zm, x, vm)]
    b = [q * (xi - zi) + p * vmi for xi, zi, vmi in zip(x, z, vm)]
    margins = []
    minimum_parameter = Fraction(0)
    minimum_parameter_row = None
    all_slopes_nonnegative = True
    for block, points, normals in [('f', x, a), ('g', z, b)]:
        row = []
        for j in range(1, K):
            other = shift(points, j)
            difference = [pi-oi for pi,oi in zip(points,other)]
            row.append(sum(ni*di for ni,di in zip(normals,difference)))
            if block == 'f':
                intercept = sum((zmi-xi)*di for zmi,xi,di in zip(zm,x,difference))
                slope = -sum(vmi*di for vmi,di in zip(vm,difference))
            else:
                intercept = sum((xi-zi)*di for xi,zi,di in zip(x,z,difference))
                slope = sum(vmi*di for vmi,di in zip(vm,difference))
            assert row[-1] == q*intercept+p*slope
            all_slopes_nonnegative &= slope >= 0
            if slope > 0 and -Fraction(intercept,slope) > minimum_parameter:
                minimum_parameter = -Fraction(intercept,slope)
                minimum_parameter_row = [block,j]
            if slope == 0:
                assert intercept >= 0
        margins.append(row)
    assert min(margins[0]) > 0, ('f', min(margins[0]))
    assert min(margins[1]) > 0, ('g', min(margins[1]))
    assert sum(z) == sum(v) == 0
    residual_squared = sum((vi - vmi)**2 for vi, vmi in zip(v, vm))
    assert residual_squared > 0
    assert all_slopes_nonnegative
    assert minimum_parameter <= tau
    # At the exact endpoint every margin remains nonnegative, which suffices
    # for the projection characterization; uniqueness comes from the squared
    # Euclidean projection objective, not strict normal inequalities.
    p0,q0 = minimum_parameter.numerator,minimum_parameter.denominator
    for block, points in [('f',x),('g',z)]:
        normals = ([q0*(zmi-xi)-p0*vmi for zmi,xi,vmi in zip(zm,x,vm)]
                   if block == 'f' else
                   [q0*(xi-zi)+p0*vmi for xi,zi,vmi in zip(x,z,vm)])
        for j in range(1,K):
            assert sum(ni*(pi-oi) for ni,pi,oi in zip(normals,points,shift(points,j))) >= 0
    return dict(period=K, ambient_dimension=K,
                minimum_f_margin=min(margins[0]),
                minimum_g_margin=min(margins[1]),
                residual_squared=residual_squared,
                squared_z_norm=sum(zi**2 for zi in z),
                all_parameter_slopes_nonnegative=all_slopes_nonnegative,
                valid_for_all_tau_at_least=str(minimum_parameter),
                active_endpoint_inequality=minimum_parameter_row,
                f_margins=margins[0], g_margins=margins[1])


def reconstruct(source, index, tau, scale):
    import numpy as np
    rows = json.loads(Path(source).read_text())
    row = rows[index]
    K = row['K']
    zz = np.zeros(K, dtype=complex)
    vv = np.zeros(K, dtype=complex)
    for j, (a, b, x, y) in enumerate(row['blocks'], 1):
        H = np.array([[a, x + 1j*y], [x - 1j*y, b]])
        ev, Q = np.linalg.eigh(H)
        # A rank-one projection is merely a candidate-generation choice.
        f = np.sqrt(max(ev[-1], 0)) * Q[:, -1].conj()
        fac = np.sqrt(K if 2*j == K else K/2)
        zz[j], vv[j] = fac*f[0], fac*f[1]
        if 2*j != K:
            zz[-j], vv[-j] = zz[j].conjugate(), vv[j].conjugate()
    zr, vr = np.fft.ifft(zz).real, np.fft.ifft(vv).real
    z = [int(round(float(t)*scale)) for t in zr]
    v = [int(round(float(t)*scale)) for t in vr]
    # Preserve exact cyclic geometry while centering each orbit.
    sz, sv = sum(z), sum(v)
    z = [K*t-sz for t in z]
    v = [K*t-sv for t in v]
    proof = check(z, v, tau)
    return dict(status='Exact integer diagnostic; not a sharp-threshold result',
                source=str(source), source_index=index,
                tau=str(tau), z_base=z, v_base=v,
                construction='State i is the left cyclic shift by i of each base vector; u=tau*v.',
                exact_check=proof)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--source')
    p.add_argument('--index', type=int, default=-2)
    p.add_argument('--tau', default='18869/10000')
    p.add_argument('--scale', type=int, default=10**9)
    p.add_argument('--output')
    p.add_argument('--check')
    a = p.parse_args()
    if a.check:
        r = json.loads(Path(a.check).read_text())
        proof = check(r['z_base'], r['v_base'], Fraction(r['tau']))
        assert proof == r['exact_check']
    else:
        r = reconstruct(a.source, a.index, Fraction(a.tau), a.scale)
        Path(a.output).write_text(json.dumps(r, indent=2)+'\n')
        proof = r['exact_check']
    print(json.dumps({k:v for k,v in proof.items() if not isinstance(v,list)}, indent=2))


if __name__ == '__main__':
    main()

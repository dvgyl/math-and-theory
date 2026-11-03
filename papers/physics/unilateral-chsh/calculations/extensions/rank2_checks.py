"""Reproduce the independent 1,000-state rank-two normal-form audit."""
import json
from pathlib import Path

import numpy as np

if __package__:
    from .independent_checks import I3, canonical, data, random_state, shortcut
else:
    from independent_checks import I3, canonical, data, random_state, shortcut


def main():
    rng = np.random.default_rng(2406394502)
    errors = []
    gram_errors = []
    guard = 0
    max_effect_norm = 0.0
    max_saturation_error = 0.0
    for _ in range(1000):
        rho, _ = canonical(random_state(rng, 2))
        c, D, A, s, d, C, K = data(rho)
        alpha = np.trace(A)-s
        m = (alpha-1)/2
        vals = np.linalg.eigvalsh(A)
        max_saturation_error = max(max_saturation_error,
            abs(np.trace(A)+s-1-2*vals[0]))
        ge = np.linalg.eigvalsh(K-m*I3+1j*C)
        gram_errors.append(max(abs(ge[0]),abs(ge[1])))
        if alpha>1:
            guard += 1
            value, u, *_ = shortcut(rho)
            errors.append(abs(value-(1+alpha)/2))
            max_effect_norm=max(max_effect_norm,np.linalg.norm(u))
    result={"seed":2406394502,"rank2_states":1000,"purity_positive":guard,
            "ceiling_error":max(errors),"optimal_effect_norm_max":max_effect_norm,
            "gram_rank1_error":max(gram_errors),
            "physicality_saturation_error":max_saturation_error}
    assert result["ceiling_error"]<1e-10
    assert result["optimal_effect_norm_max"]<1e-8
    assert result["gram_rank1_error"]<1e-10
    assert result["physicality_saturation_error"]<1e-10
    Path(__file__).with_name("rank2_scan.json").write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()

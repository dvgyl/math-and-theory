#!/usr/bin/env python3
"""Generate and check the finite extreme-ray separating certificate.

This is an independently executable integer certificate, not a substitute for
the general scalar cone inequality and tensor obstruction proved in Lean.
No optimization, numerical tolerance, assertion, or third-party module is used.
"""

import argparse
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def certificate():
    twist = [[1, 1, -1, -1], [-1, 1, 1, -1],
             [-1, -1, 1, 1], [1, -1, -1, 1]]
    rays = [[int(j == i or j == (i+1) % 4) for j in range(4)] for i in range(4)]
    scores = [[sum(u[i]*twist[i][j]*v[j] for i in range(4) for j in range(4))
               for v in rays] for u in rays]
    require(all(u[0]+u[2] == u[1]+u[3] and min(u) >= 0 for u in rays),
            "generator not in intrinsic cone")
    require(all(sum(u) == 2 for u in rays), "generator mass mismatch")
    require(all(s <= 2 for row in scores for s in row), "separating inequality failed")
    seed = [[9+8*twist[i][j] for j in range(4)] for i in range(4)]
    mass = sum(map(sum, seed))
    score = sum(twist[i][j]*seed[i][j] for i in range(4) for j in range(4))
    require(score == 128 and mass == 144 and 2*score > mass,
            "original seed does not violate cone bound")
    return {"status": "PASS", "twist": twist, "extreme_generators": rays,
            "generator_pair_scores": scores, "generator_pair_count": 16,
            "generator_pair_score_upper_bound": 2,
            "original_seed": seed, "original_seed_mass": mass,
            "original_seed_score": score,
            "original_seed_score_minus_half_mass": score-mass//2}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", type=Path)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    result = certificate()
    if args.check:
        require(json.loads(args.check.read_text()) == result,
                "saved certificate differs from independent integer computation")
    rendered = json.dumps(result, indent=2) + "\n"
    if args.write:
        args.write.write_text(rendered)
    print(rendered, end="")

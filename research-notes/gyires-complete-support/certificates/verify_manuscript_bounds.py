"""Check the rational bounds in the manuscript's limitations section."""
from fractions import Fraction as F
from pathlib import Path
import json
import sys

root = Path(__file__).parent
sys.path.insert(0, str(root / 'run'))
import round4_zero_pure_certificate as zero

base = zero.base_certificate()
unique = zero.unique_zero_certificate()
assert F(base['scaled_deletion_fock_interval'][1]) / F(base['threshold']) < F(95, 100)
assert F(unique['scaled_deletion_fock_interval'][1]) / F(unique['threshold']) < F(956, 1000)
for bounds, coarse in zip(unique['krawczyk_image_box'],
                         [(F(9789782, 10**7), F(9789784, 10**7)),
                          (F(9584771, 10**7), F(9584773, 10**7))]):
    assert coarse[0] < F(bounds[0]) <= F(bounds[1]) < coarse[1]

# Evaluate the stated binomial-noise counterexample directly from four bits.
from itertools import product
kappa = F(3, 7)
initial = (1, 1, 0, 0)
probability = F(0)
for final in product((0, 1), repeat=4):
    if sum(final) != 2:
        continue
    term = F(1)
    for x, y in zip(initial, final):
        term *= (1+kappa)/2 if x == y else (1-kappa)/2
    probability += term
noise_norm = probability / F(3, 8)
assert noise_norm == F(2776, 2401)
assert F(8, 7) < noise_norm < F(64, 49)

result = {'status': 'all exact rational assertions passed',
          'base_deletion_upper_bound': '95/100',
          'unique_zero_deletion_upper_bound': '956/1000',
          'coarsened_interval_self_map': True,
          'direct_bit_noise_norm': str(noise_norm)}
(root / 'manuscript-bounds.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))

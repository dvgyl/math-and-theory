from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import json
import platform

out = {'python': platform.python_version(), 'checks': []}
counts = [1]
motzkin = [1]
for n in range(1, 301):
    next_counts = [0] * (n + 1)
    for h, count in enumerate(counts):
        next_counts[h] += count
        next_counts[h + 1] += count
        if h:
            next_counts[h - 1] += count
    counts = next_counts
    motzkin.append(counts[0])
alternating = [sum((-1) ** (n-j) * motzkin[j] for j in range(n+1)) for n in range(301)]
data = {}
for line in Path(__file__).with_name('oeis-b187306.txt').read_text().splitlines():
    if line.strip() and not line.startswith('#'):
        n, v = map(int, line.split())
        data[n] = v
assert all(alternating[n] == data[n] for n in range(301))
assert all((n+3)*motzkin[n+1] == (2*n+3)*motzkin[n]+3*n*motzkin[n-1] for n in range(1,300))
for n in range(6, 101):
    assert alternating[n] ** (2*(n*n-1)) > alternating[n-1]**(n*(n+1))*alternating[n+1]**(n*(n-1))
assert alternating[5]**48 < alternating[4]**30*alternating[6]**20
out['checks'].append({'family':'motzkin', 'definition':'Nonnegative paths with level changes -1, 0, 1, followed by the original finite alternating sum.', 'oeis_range':[0,300], 'exact_root_inequality_centers':[6,100], 'sharp_failure_center':5, 'result':'PASS'})

out["limitation"]="These finite checks do not prove the infinite claim."
out["status"]="PASS"
print(json.dumps(out,indent=2))

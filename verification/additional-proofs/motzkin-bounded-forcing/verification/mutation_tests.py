#!/usr/bin/env python3
"""Negative controls: every deliberately corrupted certificate must be rejected."""
from __future__ import annotations
import argparse
from copy import deepcopy
import json
from pathlib import Path
import tempfile
from verify_extensions import verify, CertificateFailure


def run(source: Path) -> dict:
    data=json.loads(source.read_text())
    mutations=[]
    def add(name,change):
        item=deepcopy(data); change(item); mutations.append((name,item))
    add('change corner constant',lambda d:d['P'].__setitem__(0,d['P'][0]+1))
    add('change corner highest coefficient',lambda d:d['P'].__setitem__(-1,d['P'][-1]-1))
    add('change quantitative shifted coefficient',lambda d:d['quantitative_shift_at_12'].__setitem__(5,0))
    add('change lower-envelope identity',lambda d:d['envelope_lower_numerator'].__setitem__(0,0))
    add('change upper-envelope identity',lambda d:d['envelope_upper_numerator'].__setitem__(1,0))
    add('change forcing hypothesis',lambda d:d.__setitem__('forcing_bound',3))
    add('change universal starting index',lambda d:d.__setitem__('uniform_start_index',11))
    add('claim a larger quantitative constant',lambda d:d.__setitem__('quantitative_constant',900))
    add('change finite sequence value',lambda d:d['T_0_through_15'].__setitem__(15,227554))
    add('change family cubic',lambda d:d['family_ratio_polynomials']['9'].__setitem__(0,0))
    add('wrong ratio root bracket',lambda d:d['ratio_root_brackets'].__setitem__('9',[500000,500001]))
    add('wrong root-gap bracket',lambda d:d['root_gap_root_brackets'].__setitem__('5',[510000,510001]))
    add('wrong root order',lambda d:d.__setitem__('ratio_root_order',[4,6,5,7,9]))
    add('wrong strict ratio threshold',lambda d:d.__setitem__('original_sharp_ratio_tail',9))
    add('wrong strict root threshold',lambda d:d.__setitem__('original_sharp_root_tail',4))
    add('wrong coefficient convention',lambda d:d.__setitem__('coefficient_order','decreasing degree'))
    results=[]
    with tempfile.TemporaryDirectory(prefix='motzkin-corruption-') as tmp:
        path=Path(tmp)/'candidate.json'
        for name,item in mutations:
            path.write_text(json.dumps(item))
            try:
                verify(path,regressions=False)
            except CertificateFailure as exc:
                results.append({'mutation':name,'status':'rejected','reason':str(exc)})
            else:
                raise ArithmeticError('Corrupted certificate was accepted: '+name)
    return {'status':'passed','negative_control_count':len(results),'results':results,
            'scope':'Negative tests for the checker; not a proof of checker correctness.'}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--certificates',type=Path,default=Path(__file__).resolve().parents[1]/'proof/certificates.json')
    p.add_argument('--output',type=Path)
    a=p.parse_args(); text=json.dumps(run(a.certificates),indent=2)+'\n'
    if a.output: a.output.write_text(text)
    else: print(text,end='')

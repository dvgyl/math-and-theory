#!/usr/bin/env python3
"""Check exact manuscript JSON -> Lean positive-witness correspondence.
This is independent of the generator and needs only the Python standard library.
It does not replace Lean's kernel proof or the exact full PM/CI checker.
"""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parent
D=json.loads((H/'E3_all_overlap_polymatroids.json').read_text())
P=H/'e3_lean'/'InfoE3'/'Witnesses'
assert D['pattern']=='01111101110000011101001111010011011111010111111101111110111101011111010101100101'
w={}
for c in D['certificates']:
 L=c['overlap']
 values=[D['common_modular_offset']*S.bit_count()-v for S,v in enumerate(c['standardized_supermodular_values'])]
 assert len(values)==2**(10-L.bit_count())
 w[L]=values
 for i,j in enumerate(c['copy_map']):
  assert j==(i if L>>i&1 else 5+sum(not(L>>k&1) for k in range(i)))
 if L:
  source=(P/f'W{L:02d}.lean').read_text()
  match=re.search(r'def table\d+ : Array ℤ := #\[(.*?)\]',source,re.S)
  assert match, ('missing exact table',L)
  lean_values=[int(t) for t in re.findall(r'-?\d+',match[1])]
  assert lean_values==values, ('certificate/Lean mismatch',L)
  if L !=31:
   assert f'theorem witness{L:02d}_table : ∀ S' in source
   assert 'PMInt.of_local' in source
   assert f'encoding_ok_{c["ground_size"]}' in source
  else:
   assert 'table31[S.val]!' in source
for S in range(1024):
 assert w[0][S]==w[31][S%32]+w[31][(S>>5)%32]
source=(P/'W00.lean').read_text()
assert 'witness31 (sliceMask 5 0 S) + witness31 (sliceMask 5 5 S)' in source
assert '(witness31_pm.slice 0).add (witness31_pm.slice 5)' in source
result={'status':'PASS','tables_1_to_31_exact':True,'empty_overlap_direct_sum_exact':True,
 'integer_values_compared':sum(map(len,w.values())),
 'all_copy_maps_exact':True,
 'local_checks_reach_full_PMInt_via':'InfoE3.PMInt.of_local',
 'kernel_table_lookup_equality_endpoints':'witness01_table through witness30_table',
 'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(P.glob('W*.lean'))}}
print(json.dumps(result,indent=2))

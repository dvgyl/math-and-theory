from pathlib import Path
import re,json,hashlib,datetime,itertools
p=Path(__file__).resolve().parent
root=p/'e3_lean'
text=(root/'InfoE3/Defs.lean').read_text()
block=text.split('def ciRows :')[1].split('def ciZeros')[0]
rows=[tuple(map(int,t)) for t in re.findall(r'\((\d+), (\d+), (\d+), (\d+)\)',block)]
zeros=[w=='true' for w in re.findall(r'\b(?:true|false)\b',text.split('def ciZeros :')[1].split('def zeroCI')[0])]
def mask(s): return sum(1<<(int(v)-1) for v in s)
expected_human={'12':['','45'],'13':['4','5','24','25','45'],'14':['3','23','25'],'15':['3','23','24'],'23':['','45'],'24':[''],'25':['','134'],'34':['12','25'],'35':['12','24'],'45':['','3','12','23']}
expected={(int(ij[0])-1,int(ij[1])-1,mask(k)) for ij,ks in expected_human.items() for k in ks}
decoded=[]
for ai,bj,k,ab in rows:
 i=(ai^k).bit_length()-1;j=(bj^k).bit_length()-1
 assert ai==k|(1<<i) and bj==k|(1<<j) and ab==k|(1<<i)|(1<<j)
 assert i<j and not(k&((1<<i)|(1<<j))) and max(ai,bj,k,ab)<32
 decoded.append((i,j,k))
all_ci={(i,j,k) for i in range(5) for j in range(i+1,5) for k in range(32) if not(k&((1<<i)|(1<<j)))}
assert len(rows)==len(zeros)==80 and set(decoded)==all_ci and len(set(decoded))==80
actual={q for q,z in zip(decoded,zeros) if z}
assert actual==expected and len(actual)==26 and decoded[47]==(1,3,21) and not zeros[47]
data={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_manuscript_zero_set':True,'zero_count':26,'elemental_rows':80,'all_elementary_CI_exactly_once':True,'out_of_range_row_count':0,'target_row_47':[2,4,[1,3,5]],'target_is_required_nonzero':True,'Defs_sha256':hashlib.sha256(text.encode()).hexdigest(),'review_kind':'Independent literal manuscript table versus Lean source, not a compiler run'}
(p/'E3C_LEAN_SCOPE_PATTERN_CHECK.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps(data))


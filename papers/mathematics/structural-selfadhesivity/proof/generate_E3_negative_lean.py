#!/usr/bin/env python3
"""Generate a direct real-polymatroid Lean proof from the exact integer identity.

The output has no matrix feasibility assumptions: it instantiates submodularity
of the actual copied real set functions, then adds the displayed inequalities.
"""
from pathlib import Path
import json,itertools

ROOT=Path(__file__).resolve().parent
c=json.loads((ROOT/'E3_dual_certificate.json').read_text())

def cis(n):
    for i,j in itertools.combinations(range(n),2):
        rest=[x for x in range(n) if x not in(i,j)]
        for k in range(n-1):
            for t in itertools.combinations(rest,k):yield i,j,sum(1<<x for x in t)
base=list(cis(5))
def tuple_ci(ci):
    i,j,K=ci
    return K|1<<i,K|1<<j,K,K|1<<i|1<<j
def expr(fun,t):
    a,b,k,u=t
    return f'({fun} {a} + {fun} {b} - {fun} {k} - {fun} {u})'
def copy_map(L):
    nxt=5;out=[]
    for i in range(5):
        if L>>i&1:out.append(i)
        else:out.append(nxt);nxt+=1
    return out
def to_base(L,S):
    if S&31==S:return ('left',S)
    cp=copy_map(L);C=sum(1<<i for i in cp)
    if S&C==S:return ('right',sum(1<<i for i,x in enumerate(cp) if S>>x&1))
    return None

def is_base_row(r):
    return all(S < 32 for S in tuple_ci(r['ci_local']))

Ls=sorted({r['overlap'] for r in c['inequalities'] if not is_base_row(r)}|
          {r['overlap'] for r in c['equalities'] if r['kind']=='group'})
text=['import InfoE3.Defs','import Mathlib.Tactic.Linarith','import Mathlib.Tactic.Ring',
      'import Mathlib.Tactic.NormNum','',
      'set_option maxRecDepth 1000000','set_option maxHeartbeats 0',
      'set_option Elab.async false','',
      'namespace InfoE3','',
      '/-- The prescribed CI model has no numerically self-adhesive real-valued',
      'polymatroid realization. The proof uses only literal submodularity,',
      'normalization, equal numerical copy restrictions, and two adhesions. -/',
      'theorem no_selfadhesive_inducer : ¬ HasSelfAdhesiveInducer := by',
      '  rintro ⟨h, hp, hm, hs⟩']
for L in Ls:
    text.append(f'  obtain ⟨g{L}, p{L}, l{L}, r{L}, a{L}⟩ := hs ({L} : Mask 5)')

allvalues={L:set() for L in Ls}
terms=[]
for k,row in enumerate(c['inequalities']):
    L=row['overlap'];t=tuple_ci(row['ci_local'])
    in_base=is_base_row(row)
    n=5 if in_base else 10-L.bit_count()
    fname='h' if in_base else f'g{L}'
    pname='hp' if in_base else f'p{L}'
    a,b,K,u=t;E=expr(fname,t);terms.append((row['coefficient'],E))
    if not in_base:allvalues[L].update(t)
    text += [f'  have n{k} : 0 ≤ {E} := by',
             f'    have hh := {pname}.submod ({a} : Mask {n}) ({b} : Mask {n})',
             f'    change {fname} {K} + {fname} {u} ≤ {fname} {a} + {fname} {b} at hh',
             '    linarith only [hh]']

base_zeros=[];group_terms=[]
for row in c['equalities']:
    if row['kind']=='base_CI':
        idx=row['base_ci_index'];E=expr('h',tuple_ci(base[idx]))
        base_zeros.append((idx,-row['coefficient'],E))
        text += [f'  have z{idx} : {E} = 0 := by',
                 f'    have hh := (hm ({idx} : Fin 80)).mpr (by decide)',
                 f'    change {E} = 0 at hh', '    exact hh']
    else:
        L=row['overlap'];cp=copy_map(L);C=sum(1<<i for i in cp);U=C|31
        G=f'(g{L} 31 + g{L} {C} - g{L} {U} - g{L} {L})'
        group_terms.append((L,-row['coefficient'],G))
        allvalues[L].update([31,C,U,L])
        text += [f'  have eadh{L} : {G} = 0 := by',
                 f'    change g{L} 31 + g{L} {C} = g{L} {U} + g{L} {L} at a{L}',
                 f'    linarith only [a{L}]']

rewrites=[]
for L in Ls:
    for S in sorted(allvalues[L]):
        b=to_base(L,S)
        if b is None:continue
        side,T=b;name=f'v{L}_{S}';rewrites.append(name)
        f='l' if side=='left' else 'r'
        text += [f'  have {name} : g{L} {S} = h {T} := by',
                 f'    have hh := congrFun {f}{L} ({T} : Mask 5)',
                 f'    change g{L} {S} = h {T} at hh', '    exact hh']

def weighted(q,E):return E if q==1 else f'{q} * {E}'
sumexpr=' + '.join(weighted(q,E) for q,E in terms)
rhs=' + '.join(weighted(q,E) for idx,q,E in base_zeros)+ ' + '+ ' + '.join(weighted(q,E) for L,q,E in group_terms)
target=expr('h',tuple_ci(base[47]))
text += [f'  have hsum : 0 ≤ {sumexpr} := by']
proofs=[f'n{k}' if q==1 else f'(mul_nonneg (by norm_num) n{k})' for k,(q,E) in enumerate(terms)]
proof=proofs[0]
for p in proofs[1:]:proof=f'(add_nonneg {proof} {p})'
text.append(f'    exact {proof}')
text += [f'  have hid : {target} + ({sumexpr}) = {rhs} := by',
         '    simp only ['+', '.join(rewrites)+', hp.empty]',
         '    ring',
         f'  have hz : {target} = 0 := by',
         '    have nn := hp.submod (23 : Mask 5) (29 : Mask 5)',
         '    change h 21 + h 31 ≤ h 23 + h 29 at nn',
         '    linarith only [hid, hsum, nn, '+', '.join('z'+str(i) for i,q,E in base_zeros)+', '+', '.join('eadh'+str(L) for L,q,E in group_terms)+']',
         '  have bad := (hm (47 : Fin 80)).mp (show cmi h 47 = 0 from hz)',
         '  change false = true at bad',
         '  cases bad','',
         '#print axioms no_selfadhesive_inducer','',
         'end InfoE3','']
(ROOT/'e3_lean/InfoE3/Negative.lean').write_text('\n'.join(text))
print('Generated',len(text),'lines; explicit elemental inequalities',len(terms))

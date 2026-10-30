#!/usr/bin/env python3
"""Generate exact local certificates feeding a proved full polymatroid theorem.
All reductions use Lean's kernel. No solver, native reduction, or new axiom.
W00 has an independent algebraic direct-sum proof and is preserved.
"""
import json,sys
from pathlib import Path
H=Path(__file__).resolve().parent
D=json.loads((H/'E3_all_overlap_polymatroids.json').read_text())
P=H/'e3_lean'/'InfoE3'/'Witnesses'

def tree(a,lo=0):
 if len(a)==1:return str(a[0])
 k=len(a)//2
 return f'(if s < {lo+k} then {tree(a[:k],lo)} else {tree(a[k:],lo+k)})'

def emit(L):
 c=next(c for c in D['certificates'] if c['overlap']==L)
 name=f'{L:02d}';n=c['ground_size'];N=2**n
 a=[D['common_modular_offset']*i.bit_count()-v for i,v in enumerate(c['standardized_supermodular_values'])]
 lines=[', '.join(map(str,a[j:j+16])) for j in range(0,N,16)]
 t=',\n  '.join(lines)
 s=f'''import InfoE3.PositiveBase
import InfoE3.LocalPM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace InfoE3

def table{name} : Array ℤ := #[
  {t}
]

/-- Balanced literal lookup of the exact integer certificate. -/
def lookup{name} (s : Nat) : ℤ := {tree(a)}
def witness{name} (S : Mask (groundSize {L})) : ℤ := lookup{name} S.val

theorem witness{name}_table : ∀ S : Mask (groundSize {L}),
    witness{name} S = table{name}[S.val]! := by decide +kernel

theorem witness{name}_local_mono : MaskLocalMono witness{name} := by
  unfold MaskLocalMono
  decide +kernel

theorem witness{name}_local_squares : MaskLocalSquares witness{name} := by
  unfold MaskLocalSquares
  decide +kernel

theorem witness{name}_pm : PMInt (groundSize {L}) witness{name} :=
  PMInt.of_local encoding_ok_{n} (by decide +kernel)
    witness{name}_local_mono witness{name}_local_squares

theorem witness{name}_first : MatchesInt (fun S => witness{name} (origMask {L} S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness{name}_second : MatchesInt (fun S => witness{name} (copyMask {L} S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness{name}_adhesive : AdhesiveInt {L} witness{name} := by
  unfold AdhesiveInt
  decide +kernel

theorem structural_at_{name} : ∃ g : Mask (groundSize {L}) → ℝ,
    PM (groundSize {L}) g ∧ Matches (firstRestrict {L} g) ∧
    Matches (secondRestrict {L} g) ∧ Adhesive {L} g :=
  positive_of_int {L} witness{name} witness{name}_pm witness{name}_first witness{name}_second witness{name}_adhesive

#print axioms witness{name}_pm
end InfoE3
'''
 (P/f'W{name}.lean').write_text(s)
for L in (list(map(int,sys.argv[1:])) if len(sys.argv)>1 else range(1,31)):
 assert L!=0
 emit(L)
 print('generated',L)

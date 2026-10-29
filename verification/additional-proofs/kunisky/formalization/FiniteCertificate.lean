import Resolution

namespace Kunisky.FiniteCounterexample

noncomputable section

abbrev C3 := Clause (Fin 3)

def clauses : Fin 8 → C3 := ![{(0, true), (1, true), (2, true)}, {(0, true), (1, true), (2, false)}, {(0, true), (1, false), (2, true)}, {(0, true), (1, false), (2, false)}, {(0, false), (1, true), (2, true)}, {(0, false), (1, true), (2, false)}, {(0, false), (1, false), (2, true)}, {(0, false), (1, false), (2, false)}]

def F : Finset C3 := fullFormula 3

def Certified (t : Tree (Fin 3)) (C : C3) (w : Fin 8 → ℝ) : Prop :=
  t.Valid F ∧ t.conclusion = C ∧ ∀ i, t.mass (clauses i) = w i

lemma certified_node {v : Fin 3} {l r : Tree (Fin 3)} {L R C : C3}
    {a b w : Fin 8 → ℝ} (hl : Certified l L a) (hr : Certified r R b)
    (hpl : (v,true) ∈ L) (hpr : (v,false) ∈ R)
    (hc : L.erase (v,true) ∪ R.erase (v,false) = C)
    (hw : ∀ i, (a i + b i)/2 = w i) : Certified (.node v l r) C w := by
  rcases hl with ⟨hvl,hcl,hml⟩
  rcases hr with ⟨hvr,hcr,hmr⟩
  refine ⟨⟨hvl,hvr,?_,?_⟩,?_,?_⟩
  · simpa [hcl] using hpl
  · simpa [hcr] using hpr
  · simpa [Tree.conclusion,hcl,hcr] using hc
  · intro i
    simpa [Tree.mass,hml,hmr] using hw i

def w0 : Fin 8 → ℝ := ![1, 0, 0, 0, 0, 0, 0, 0]
def t0 : Tree (Fin 3) := .leaf (clauses 0)
theorem cert0 : Certified t0 ({(0, true), (1, true), (2, true)}) w0 := by
  refine ⟨?_, rfl, ?_⟩
  · change clauses 0 ∈ F
    decide
  intro j
  fin_cases j <;> norm_num [t0, Tree.mass, clauses, w0] <;> decide

def w1 : Fin 8 → ℝ := ![0, 1, 0, 0, 0, 0, 0, 0]
def t1 : Tree (Fin 3) := .leaf (clauses 1)
theorem cert1 : Certified t1 ({(0, true), (1, true), (2, false)}) w1 := by
  refine ⟨?_, rfl, ?_⟩
  · change clauses 1 ∈ F
    decide
  intro j
  fin_cases j <;> norm_num [t1, Tree.mass, clauses, w1] <;> decide

def w2 : Fin 8 → ℝ := ![0, 0, 1, 0, 0, 0, 0, 0]
def t2 : Tree (Fin 3) := .leaf (clauses 2)
theorem cert2 : Certified t2 ({(0, true), (1, false), (2, true)}) w2 := by
  refine ⟨?_, rfl, ?_⟩
  · change clauses 2 ∈ F
    decide
  intro j
  fin_cases j <;> norm_num [t2, Tree.mass, clauses, w2] <;> decide

def w3 : Fin 8 → ℝ := ![0, 0, 0, 1, 0, 0, 0, 0]
def t3 : Tree (Fin 3) := .leaf (clauses 3)
theorem cert3 : Certified t3 ({(0, true), (1, false), (2, false)}) w3 := by
  refine ⟨?_, rfl, ?_⟩
  · change clauses 3 ∈ F
    decide
  intro j
  fin_cases j <;> norm_num [t3, Tree.mass, clauses, w3] <;> decide

def w4 : Fin 8 → ℝ := ![0, 0, 0, 0, 1, 0, 0, 0]
def t4 : Tree (Fin 3) := .leaf (clauses 4)
theorem cert4 : Certified t4 ({(0, false), (1, true), (2, true)}) w4 := by
  refine ⟨?_, rfl, ?_⟩
  · change clauses 4 ∈ F
    decide
  intro j
  fin_cases j <;> norm_num [t4, Tree.mass, clauses, w4] <;> decide

def w5 : Fin 8 → ℝ := ![0, 0, 0, 0, 0, 1, 0, 0]
def t5 : Tree (Fin 3) := .leaf (clauses 5)
theorem cert5 : Certified t5 ({(0, false), (1, true), (2, false)}) w5 := by
  refine ⟨?_, rfl, ?_⟩
  · change clauses 5 ∈ F
    decide
  intro j
  fin_cases j <;> norm_num [t5, Tree.mass, clauses, w5] <;> decide

def w6 : Fin 8 → ℝ := ![0, 0, 0, 0, 0, 0, 1, 0]
def t6 : Tree (Fin 3) := .leaf (clauses 6)
theorem cert6 : Certified t6 ({(0, false), (1, false), (2, true)}) w6 := by
  refine ⟨?_, rfl, ?_⟩
  · change clauses 6 ∈ F
    decide
  intro j
  fin_cases j <;> norm_num [t6, Tree.mass, clauses, w6] <;> decide

def w7 : Fin 8 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 1]
def t7 : Tree (Fin 3) := .leaf (clauses 7)
theorem cert7 : Certified t7 ({(0, false), (1, false), (2, false)}) w7 := by
  refine ⟨?_, rfl, ?_⟩
  · change clauses 7 ∈ F
    decide
  intro j
  fin_cases j <;> norm_num [t7, Tree.mass, clauses, w7] <;> decide

def w8 : Fin 8 → ℝ := ![(1 / 2), 0, 0, 0, (1 / 2), 0, 0, 0]
def t8 : Tree (Fin 3) := .node 0 t0 t4
theorem cert8 : Certified t8 ({(1, true), (2, true)}) w8 := by
  apply certified_node cert0 cert4 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w4, w8]

def w9 : Fin 8 → ℝ := ![0, 0, 0, (1 / 2), 0, 0, 0, (1 / 2)]
def t9 : Tree (Fin 3) := .node 0 t3 t7
theorem cert9 : Certified t9 ({(1, false), (2, false)}) w9 := by
  apply certified_node cert3 cert7 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w3, w7, w9]

def w10 : Fin 8 → ℝ := ![(1 / 2), 0, (1 / 2), 0, 0, 0, 0, 0]
def t10 : Tree (Fin 3) := .node 1 t0 t2
theorem cert10 : Certified t10 ({(0, true), (2, true)}) w10 := by
  apply certified_node cert0 cert2 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w2, w10]

def w11 : Fin 8 → ℝ := ![(1 / 2), (1 / 2), 0, 0, 0, 0, 0, 0]
def t11 : Tree (Fin 3) := .node 2 t0 t1
theorem cert11 : Certified t11 ({(0, true), (1, true)}) w11 := by
  apply certified_node cert0 cert1 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w1, w11]

def w12 : Fin 8 → ℝ := ![0, 0, 0, 0, 0, (1 / 2), 0, (1 / 2)]
def t12 : Tree (Fin 3) := .node 1 t5 t7
theorem cert12 : Certified t12 ({(0, false), (2, false)}) w12 := by
  apply certified_node cert5 cert7 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w5, w7, w12]

def w13 : Fin 8 → ℝ := ![0, 0, 0, 0, 0, 0, (1 / 2), (1 / 2)]
def t13 : Tree (Fin 3) := .node 2 t6 t7
theorem cert13 : Certified t13 ({(0, false), (1, false)}) w13 := by
  apply certified_node cert6 cert7 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w6, w7, w13]

def w14 : Fin 8 → ℝ := ![(1 / 4), (1 / 4), 0, 0, 0, (1 / 4), 0, (1 / 4)]
def t14 : Tree (Fin 3) := .node 0 t11 t12
theorem cert14 : Certified t14 ({(1, true), (2, false)}) w14 := by
  apply certified_node cert11 cert12 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w11, w12, w14]

def w15 : Fin 8 → ℝ := ![(1 / 4), 0, (1 / 4), 0, 0, 0, (1 / 4), (1 / 4)]
def t15 : Tree (Fin 3) := .node 0 t10 t13
theorem cert15 : Certified t15 ({(1, false), (2, true)}) w15 := by
  apply certified_node cert10 cert13 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w10, w13, w15]

def w16 : Fin 8 → ℝ := ![(1 / 4), 0, (1 / 4), (1 / 4), 0, 0, 0, (1 / 4)]
def t16 : Tree (Fin 3) := .node 2 t10 t9
theorem cert16 : Certified t16 ({(0, true), (1, false)}) w16 := by
  apply certified_node cert10 cert9 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w10, w9, w16]

def w17 : Fin 8 → ℝ := ![(1 / 4), 0, 0, 0, (1 / 4), 0, (1 / 4), (1 / 4)]
def t17 : Tree (Fin 3) := .node 1 t8 t13
theorem cert17 : Certified t17 ({(0, false), (2, true)}) w17 := by
  apply certified_node cert8 cert13 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w8, w13, w17]

def w18 : Fin 8 → ℝ := ![(1 / 4), 0, 0, 0, (1 / 4), (1 / 4), 0, (1 / 4)]
def t18 : Tree (Fin 3) := .node 2 t8 t12
theorem cert18 : Certified t18 ({(0, false), (1, true)}) w18 := by
  apply certified_node cert8 cert12 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w8, w12, w18]

def w19 : Fin 8 → ℝ := ![(5 / 8), 0, 0, 0, (1 / 8), 0, (1 / 8), (1 / 8)]
def t19 : Tree (Fin 3) := .node 0 t0 t17
theorem cert19 : Certified t19 ({(1, true), (2, true)}) w19 := by
  apply certified_node cert0 cert17 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w17, w19]

def w20 : Fin 8 → ℝ := ![(1 / 8), 0, (1 / 8), (1 / 8), 0, (1 / 4), 0, (3 / 8)]
def t20 : Tree (Fin 3) := .node 0 t16 t12
theorem cert20 : Certified t20 ({(1, false), (2, false)}) w20 := by
  apply certified_node cert16 cert12 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w16, w12, w20]

def w21 : Fin 8 → ℝ := ![(5 / 8), 0, (1 / 8), 0, 0, 0, (1 / 8), (1 / 8)]
def t21 : Tree (Fin 3) := .node 1 t0 t15
theorem cert21 : Certified t21 ({(0, true), (2, true)}) w21 := by
  apply certified_node cert0 cert15 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w15, w21]

def w22 : Fin 8 → ℝ := ![(5 / 8), (1 / 8), 0, 0, 0, (1 / 8), 0, (1 / 8)]
def t22 : Tree (Fin 3) := .node 2 t0 t14
theorem cert22 : Certified t22 ({(0, true), (1, true)}) w22 := by
  apply certified_node cert0 cert14 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w14, w22]

def w23 : Fin 8 → ℝ := ![(1 / 8), 0, 0, (1 / 4), (1 / 8), (1 / 8), 0, (3 / 8)]
def t23 : Tree (Fin 3) := .node 1 t18 t9
theorem cert23 : Certified t23 ({(0, false), (2, false)}) w23 := by
  apply certified_node cert18 cert9 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w18, w9, w23]

def w24 : Fin 8 → ℝ := ![(1 / 8), 0, 0, (1 / 4), (1 / 8), 0, (1 / 8), (3 / 8)]
def t24 : Tree (Fin 3) := .node 2 t17 t9
theorem cert24 : Certified t24 ({(0, false), (1, false)}) w24 := by
  apply certified_node cert17 cert9 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w17, w9, w24]

def w25 : Fin 8 → ℝ := ![(3 / 8), (1 / 16), 0, (1 / 8), (1 / 16), (1 / 8), 0, (1 / 4)]
def t25 : Tree (Fin 3) := .node 0 t22 t23
theorem cert25 : Certified t25 ({(1, true), (2, false)}) w25 := by
  apply certified_node cert22 cert23 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w22, w23, w25]

def w26 : Fin 8 → ℝ := ![(3 / 8), 0, (1 / 16), (1 / 8), (1 / 16), 0, (1 / 8), (1 / 4)]
def t26 : Tree (Fin 3) := .node 0 t21 t24
theorem cert26 : Certified t26 ({(1, false), (2, true)}) w26 := by
  apply certified_node cert21 cert24 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w21, w24, w26]

def w27 : Fin 8 → ℝ := ![(3 / 16), 0, (1 / 8), (1 / 4), (1 / 16), (1 / 16), 0, (5 / 16)]
def t27 : Tree (Fin 3) := .node 0 t16 t23
theorem cert27 : Certified t27 ({(1, false), (2, false)}) w27 := by
  apply certified_node cert16 cert23 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w16, w23, w27]

def w28 : Fin 8 → ℝ := ![(3 / 8), 0, (1 / 8), (1 / 16), 0, (1 / 8), (1 / 16), (1 / 4)]
def t28 : Tree (Fin 3) := .node 2 t21 t20
theorem cert28 : Certified t28 ({(0, true), (1, false)}) w28 := by
  apply certified_node cert21 cert20 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w21, w20, w28]

def w29 : Fin 8 → ℝ := ![(3 / 8), 0, 0, (1 / 8), (1 / 8), 0, (1 / 8), (1 / 4)]
def t29 : Tree (Fin 3) := .node 1 t19 t24
theorem cert29 : Certified t29 ({(0, false), (2, true)}) w29 := by
  apply certified_node cert19 cert24 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w19, w24, w29]

def w30 : Fin 8 → ℝ := ![(3 / 16), 0, (1 / 16), (1 / 16), (1 / 8), (1 / 4), 0, (5 / 16)]
def t30 : Tree (Fin 3) := .node 1 t18 t20
theorem cert30 : Certified t30 ({(0, false), (2, false)}) w30 := by
  apply certified_node cert18 cert20 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w18, w20, w30]

def w31 : Fin 8 → ℝ := ![(3 / 8), 0, 0, (1 / 8), (1 / 8), (1 / 16), (1 / 16), (1 / 4)]
def t31 : Tree (Fin 3) := .node 2 t19 t23
theorem cert31 : Certified t31 ({(0, false), (1, true)}) w31 := by
  apply certified_node cert19 cert23 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w19, w23, w31]

def w32 : Fin 8 → ℝ := ![(3 / 16), 0, (1 / 16), (1 / 16), (1 / 8), (1 / 8), (1 / 8), (5 / 16)]
def t32 : Tree (Fin 3) := .node 2 t17 t20
theorem cert32 : Certified t32 ({(0, false), (1, false)}) w32 := by
  apply certified_node cert17 cert20 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w17, w20, w32]

def w33 : Fin 8 → ℝ := ![(11 / 16), 0, 0, (1 / 16), (1 / 16), 0, (1 / 16), (1 / 8)]
def t33 : Tree (Fin 3) := .node 0 t0 t29
theorem cert33 : Certified t33 ({(1, true), (2, true)}) w33 := by
  apply certified_node cert0 cert29 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w29, w33]

def w34 : Fin 8 → ℝ := ![(13 / 32), (1 / 16), (1 / 32), (1 / 32), (1 / 16), (3 / 16), 0, (7 / 32)]
def t34 : Tree (Fin 3) := .node 0 t22 t30
theorem cert34 : Certified t34 ({(1, true), (2, false)}) w34 := by
  apply certified_node cert22 cert30 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w22, w30, w34]

def w35 : Fin 8 → ℝ := ![(13 / 32), 0, (3 / 32), (1 / 32), (1 / 16), (1 / 16), (1 / 8), (7 / 32)]
def t35 : Tree (Fin 3) := .node 0 t21 t32
theorem cert35 : Certified t35 ({(1, false), (2, true)}) w35 := by
  apply certified_node cert21 cert32 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w21, w32, w35]

def w36 : Fin 8 → ℝ := ![(9 / 32), 0, (3 / 32), (1 / 16), (1 / 16), (3 / 16), (1 / 32), (9 / 32)]
def t36 : Tree (Fin 3) := .node 0 t28 t30
theorem cert36 : Certified t36 ({(1, false), (2, false)}) w36 := by
  apply certified_node cert28 cert30 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w28, w30, w36]

def w37 : Fin 8 → ℝ := ![(11 / 16), 0, (1 / 32), (1 / 16), (1 / 32), 0, (1 / 16), (1 / 8)]
def t37 : Tree (Fin 3) := .node 1 t0 t26
theorem cert37 : Certified t37 ({(0, true), (2, true)}) w37 := by
  apply certified_node cert0 cert26 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w26, w37]

def w38 : Fin 8 → ℝ := ![(11 / 16), (1 / 32), 0, (1 / 16), (1 / 32), (1 / 16), 0, (1 / 8)]
def t38 : Tree (Fin 3) := .node 2 t0 t25
theorem cert38 : Certified t38 ({(0, true), (1, true)}) w38 := by
  apply certified_node cert0 cert25 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w25, w38]

def w39 : Fin 8 → ℝ := ![(13 / 32), 0, (1 / 8), (1 / 8), (1 / 32), (1 / 32), (1 / 16), (7 / 32)]
def t39 : Tree (Fin 3) := .node 2 t21 t27
theorem cert39 : Certified t39 ({(0, true), (1, false)}) w39 := by
  apply certified_node cert21 cert27 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w21, w27, w39]

def w40 : Fin 8 → ℝ := ![(13 / 32), 0, (1 / 32), (1 / 32), (1 / 8), (1 / 16), (1 / 8), (7 / 32)]
def t40 : Tree (Fin 3) := .node 1 t19 t32
theorem cert40 : Certified t40 ({(0, false), (2, true)}) w40 := by
  apply certified_node cert19 cert32 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w19, w32, w40]

def w41 : Fin 8 → ℝ := ![(9 / 32), 0, (1 / 16), (3 / 16), (3 / 32), (1 / 16), (1 / 32), (9 / 32)]
def t41 : Tree (Fin 3) := .node 1 t31 t27
theorem cert41 : Certified t41 ({(0, false), (2, false)}) w41 := by
  apply certified_node cert31 cert27 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w31, w27, w41]

def w42 : Fin 8 → ℝ := ![(13 / 32), 0, (1 / 32), (1 / 32), (1 / 8), (1 / 8), (1 / 16), (7 / 32)]
def t42 : Tree (Fin 3) := .node 2 t19 t30
theorem cert42 : Certified t42 ({(0, false), (1, true)}) w42 := by
  apply certified_node cert19 cert30 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w19, w30, w42]

def w43 : Fin 8 → ℝ := ![(9 / 32), 0, (1 / 16), (3 / 16), (3 / 32), (1 / 32), (1 / 16), (9 / 32)]
def t43 : Tree (Fin 3) := .node 2 t29 t27
theorem cert43 : Certified t43 ({(0, false), (1, false)}) w43 := by
  apply certified_node cert29 cert27 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w29, w27, w43]

def w44 : Fin 8 → ℝ := ![(45 / 64), 0, (1 / 64), (1 / 64), (1 / 16), (1 / 32), (1 / 16), (7 / 64)]
def t44 : Tree (Fin 3) := .node 0 t0 t40
theorem cert44 : Certified t44 ({(1, true), (2, true)}) w44 := by
  apply certified_node cert0 cert40 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w40, w44]

def w45 : Fin 8 → ℝ := ![(31 / 64), (1 / 64), (1 / 32), (1 / 8), (1 / 16), (1 / 16), (1 / 64), (13 / 64)]
def t45 : Tree (Fin 3) := .node 0 t38 t41
theorem cert45 : Certified t45 ({(1, true), (2, false)}) w45 := by
  apply certified_node cert38 cert41 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w38, w41, w45]

def w46 : Fin 8 → ℝ := ![(31 / 64), 0, (3 / 64), (1 / 8), (1 / 16), (1 / 64), (1 / 16), (13 / 64)]
def t46 : Tree (Fin 3) := .node 0 t37 t43
theorem cert46 : Certified t46 ({(1, false), (2, true)}) w46 := by
  apply certified_node cert37 cert43 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w37, w43, w46]

def w47 : Fin 8 → ℝ := ![(11 / 32), 0, (3 / 32), (5 / 32), (1 / 16), (3 / 64), (3 / 64), (1 / 4)]
def t47 : Tree (Fin 3) := .node 0 t39 t41
theorem cert47 : Certified t47 ({(1, false), (2, false)}) w47 := by
  apply certified_node cert39 cert41 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w39, w41, w47]

def w48 : Fin 8 → ℝ := ![(45 / 64), 0, (3 / 64), (1 / 64), (1 / 32), (1 / 32), (1 / 16), (7 / 64)]
def t48 : Tree (Fin 3) := .node 1 t0 t35
theorem cert48 : Certified t48 ({(0, true), (2, true)}) w48 := by
  apply certified_node cert0 cert35 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w35, w48]

def w49 : Fin 8 → ℝ := ![(45 / 64), (1 / 32), (1 / 64), (1 / 64), (1 / 32), (3 / 32), 0, (7 / 64)]
def t49 : Tree (Fin 3) := .node 2 t0 t34
theorem cert49 : Certified t49 ({(0, true), (1, true)}) w49 := by
  apply certified_node cert0 cert34 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w34, w49]

def w50 : Fin 8 → ℝ := ![(31 / 64), 0, (1 / 16), (1 / 16), (3 / 64), (3 / 32), (3 / 64), (13 / 64)]
def t50 : Tree (Fin 3) := .node 2 t37 t36
theorem cert50 : Certified t50 ({(0, true), (1, false)}) w50 := by
  apply certified_node cert37 cert36 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w37, w36, w50]

def w51 : Fin 8 → ℝ := ![(31 / 64), 0, (1 / 32), (1 / 8), (5 / 64), (1 / 64), (1 / 16), (13 / 64)]
def t51 : Tree (Fin 3) := .node 1 t33 t43
theorem cert51 : Certified t51 ({(0, false), (2, true)}) w51 := by
  apply certified_node cert33 cert43 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w33, w43, w51]

def w52 : Fin 8 → ℝ := ![(11 / 32), 0, (1 / 16), (3 / 64), (3 / 32), (5 / 32), (3 / 64), (1 / 4)]
def t52 : Tree (Fin 3) := .node 1 t42 t36
theorem cert52 : Certified t52 ({(0, false), (2, false)}) w52 := by
  apply certified_node cert42 cert36 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w42, w36, w52]

def w53 : Fin 8 → ℝ := ![(31 / 64), 0, (1 / 32), (1 / 8), (5 / 64), (1 / 32), (3 / 64), (13 / 64)]
def t53 : Tree (Fin 3) := .node 2 t33 t41
theorem cert53 : Certified t53 ({(0, false), (1, true)}) w53 := by
  apply certified_node cert33 cert41 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w33, w41, w53]

def w54 : Fin 8 → ℝ := ![(11 / 32), 0, (1 / 16), (3 / 64), (3 / 32), (1 / 8), (5 / 64), (1 / 4)]
def t54 : Tree (Fin 3) := .node 2 t40 t36
theorem cert54 : Certified t54 ({(0, false), (1, false)}) w54 := by
  apply certified_node cert40 cert36 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w40, w36, w54]

def w55 : Fin 8 → ℝ := ![(95 / 128), 0, (1 / 64), (1 / 16), (5 / 128), (1 / 128), (1 / 32), (13 / 128)]
def t55 : Tree (Fin 3) := .node 0 t0 t51
theorem cert55 : Certified t55 ({(1, true), (2, true)}) w55 := by
  apply certified_node cert0 cert51 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w51, w55]

def w56 : Fin 8 → ℝ := ![(67 / 128), (1 / 64), (5 / 128), (1 / 32), (1 / 16), (1 / 8), (3 / 128), (23 / 128)]
def t56 : Tree (Fin 3) := .node 0 t49 t52
theorem cert56 : Certified t56 ({(1, true), (2, false)}) w56 := by
  apply certified_node cert49 cert52 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w49, w52, w56]

def w57 : Fin 8 → ℝ := ![(67 / 128), 0, (7 / 128), (1 / 32), (1 / 16), (5 / 64), (9 / 128), (23 / 128)]
def t57 : Tree (Fin 3) := .node 0 t48 t54
theorem cert57 : Certified t57 ({(1, false), (2, true)}) w57 := by
  apply certified_node cert48 cert54 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w48, w54, w57]

def w58 : Fin 8 → ℝ := ![(53 / 128), 0, (1 / 16), (7 / 128), (9 / 128), (1 / 8), (3 / 64), (29 / 128)]
def t58 : Tree (Fin 3) := .node 0 t50 t52
theorem cert58 : Certified t58 ({(1, false), (2, false)}) w58 := by
  apply certified_node cert50 cert52 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w50, w52, w58]

def w59 : Fin 8 → ℝ := ![(95 / 128), 0, (3 / 128), (1 / 16), (1 / 32), (1 / 128), (1 / 32), (13 / 128)]
def t59 : Tree (Fin 3) := .node 1 t0 t46
theorem cert59 : Certified t59 ({(0, true), (2, true)}) w59 := by
  apply certified_node cert0 cert46 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w46, w59]

def w60 : Fin 8 → ℝ := ![(95 / 128), (1 / 128), (1 / 64), (1 / 16), (1 / 32), (1 / 32), (1 / 128), (13 / 128)]
def t60 : Tree (Fin 3) := .node 2 t0 t45
theorem cert60 : Certified t60 ({(0, true), (1, true)}) w60 := by
  apply certified_node cert0 cert45 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w45, w60]

def w61 : Fin 8 → ℝ := ![(67 / 128), 0, (9 / 128), (11 / 128), (3 / 64), (5 / 128), (7 / 128), (23 / 128)]
def t61 : Tree (Fin 3) := .node 2 t48 t47
theorem cert61 : Certified t61 ({(0, true), (1, false)}) w61 := by
  apply certified_node cert48 cert47 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w48, w47, w61]

def w62 : Fin 8 → ℝ := ![(67 / 128), 0, (5 / 128), (1 / 32), (5 / 64), (5 / 64), (9 / 128), (23 / 128)]
def t62 : Tree (Fin 3) := .node 1 t44 t54
theorem cert62 : Certified t62 ({(0, false), (2, true)}) w62 := by
  apply certified_node cert44 cert54 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w44, w54, w62]

def w63 : Fin 8 → ℝ := ![(53 / 128), 0, (1 / 16), (9 / 64), (9 / 128), (5 / 128), (3 / 64), (29 / 128)]
def t63 : Tree (Fin 3) := .node 1 t53 t47
theorem cert63 : Certified t63 ({(0, false), (2, false)}) w63 := by
  apply certified_node cert53 cert47 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w53, w47, w63]

def w64 : Fin 8 → ℝ := ![(67 / 128), 0, (5 / 128), (1 / 32), (5 / 64), (3 / 32), (7 / 128), (23 / 128)]
def t64 : Tree (Fin 3) := .node 2 t44 t52
theorem cert64 : Certified t64 ({(0, false), (1, true)}) w64 := by
  apply certified_node cert44 cert52 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w44, w52, w64]

def w65 : Fin 8 → ℝ := ![(53 / 128), 0, (1 / 16), (9 / 64), (9 / 128), (1 / 32), (7 / 128), (29 / 128)]
def t65 : Tree (Fin 3) := .node 2 t51 t47
theorem cert65 : Certified t65 ({(0, false), (1, false)}) w65 := by
  apply certified_node cert51 cert47 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w51, w47, w65]

def w66 : Fin 8 → ℝ := ![(195 / 256), 0, (5 / 256), (1 / 64), (5 / 128), (5 / 128), (9 / 256), (23 / 256)]
def t66 : Tree (Fin 3) := .node 0 t0 t62
theorem cert66 : Certified t66 ({(1, true), (2, true)}) w66 := by
  apply certified_node cert0 cert62 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w62, w66]

def w67 : Fin 8 → ℝ := ![(37 / 64), (1 / 256), (5 / 128), (13 / 128), (13 / 256), (9 / 256), (7 / 256), (21 / 128)]
def t67 : Tree (Fin 3) := .node 0 t60 t63
theorem cert67 : Certified t67 ({(1, true), (2, false)}) w67 := by
  apply certified_node cert60 cert63 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w60, w63, w67]

def w68 : Fin 8 → ℝ := ![(37 / 64), 0, (11 / 256), (13 / 128), (13 / 256), (5 / 256), (11 / 256), (21 / 128)]
def t68 : Tree (Fin 3) := .node 0 t59 t65
theorem cert68 : Certified t68 ({(1, false), (2, true)}) w68 := by
  apply certified_node cert59 cert65 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w59, w65, w68]

def w69 : Fin 8 → ℝ := ![(15 / 32), 0, (17 / 256), (29 / 256), (15 / 256), (5 / 128), (13 / 256), (13 / 64)]
def t69 : Tree (Fin 3) := .node 0 t61 t63
theorem cert69 : Certified t69 ({(1, false), (2, false)}) w69 := by
  apply certified_node cert61 cert63 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w61, w63, w69]

def w70 : Fin 8 → ℝ := ![(195 / 256), 0, (7 / 256), (1 / 64), (1 / 32), (5 / 128), (9 / 256), (23 / 256)]
def t70 : Tree (Fin 3) := .node 1 t0 t57
theorem cert70 : Certified t70 ({(0, true), (2, true)}) w70 := by
  apply certified_node cert0 cert57 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w57, w70]

def w71 : Fin 8 → ℝ := ![(195 / 256), (1 / 128), (5 / 256), (1 / 64), (1 / 32), (1 / 16), (3 / 256), (23 / 256)]
def t71 : Tree (Fin 3) := .node 2 t0 t56
theorem cert71 : Certified t71 ({(0, true), (1, true)}) w71 := by
  apply certified_node cert0 cert56 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w56, w71]

def w72 : Fin 8 → ℝ := ![(37 / 64), 0, (11 / 256), (15 / 256), (13 / 256), (17 / 256), (5 / 128), (21 / 128)]
def t72 : Tree (Fin 3) := .node 2 t59 t58
theorem cert72 : Certified t72 ({(0, true), (1, false)}) w72 := by
  apply certified_node cert59 cert58 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w59, w58, w72]

def w73 : Fin 8 → ℝ := ![(37 / 64), 0, (5 / 128), (13 / 128), (7 / 128), (5 / 256), (11 / 256), (21 / 128)]
def t73 : Tree (Fin 3) := .node 1 t55 t65
theorem cert73 : Certified t73 ({(0, false), (2, true)}) w73 := by
  apply certified_node cert55 cert65 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w55, w65, w73]

def w74 : Fin 8 → ℝ := ![(15 / 32), 0, (13 / 256), (11 / 256), (19 / 256), (7 / 64), (13 / 256), (13 / 64)]
def t74 : Tree (Fin 3) := .node 1 t64 t58
theorem cert74 : Certified t74 ({(0, false), (2, false)}) w74 := by
  apply certified_node cert64 cert58 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w64, w58, w74]

def w75 : Fin 8 → ℝ := ![(37 / 64), 0, (5 / 128), (13 / 128), (7 / 128), (3 / 128), (5 / 128), (21 / 128)]
def t75 : Tree (Fin 3) := .node 2 t55 t63
theorem cert75 : Certified t75 ({(0, false), (1, true)}) w75 := by
  apply certified_node cert55 cert63 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w55, w63, w75]

def w76 : Fin 8 → ℝ := ![(15 / 32), 0, (13 / 256), (11 / 256), (19 / 256), (13 / 128), (15 / 256), (13 / 64)]
def t76 : Tree (Fin 3) := .node 2 t62 t58
theorem cert76 : Certified t76 ({(0, false), (1, false)}) w76 := by
  apply certified_node cert62 cert58 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w62, w58, w76]

def w77 : Fin 8 → ℝ := ![(101 / 128), 0, (5 / 256), (13 / 256), (7 / 256), (5 / 512), (11 / 512), (21 / 256)]
def t77 : Tree (Fin 3) := .node 0 t0 t73
theorem cert77 : Certified t77 ({(1, true), (2, true)}) w77 := by
  apply certified_node cert0 cert73 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w73, w77]

def w78 : Fin 8 → ℝ := ![(315 / 512), (1 / 256), (9 / 256), (15 / 512), (27 / 512), (11 / 128), (1 / 32), (75 / 512)]
def t78 : Tree (Fin 3) := .node 0 t71 t74
theorem cert78 : Certified t78 ({(1, true), (2, false)}) w78 := by
  apply certified_node cert71 cert74 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w71, w74, w78]

def w79 : Fin 8 → ℝ := ![(315 / 512), 0, (5 / 128), (15 / 512), (27 / 512), (9 / 128), (3 / 64), (75 / 512)]
def t79 : Tree (Fin 3) := .node 0 t70 t76
theorem cert79 : Certified t79 ({(1, false), (2, true)}) w79 := by
  apply certified_node cert70 cert76 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w70, w76, w79]

def w80 : Fin 8 → ℝ := ![(67 / 128), 0, (3 / 64), (13 / 256), (1 / 16), (45 / 512), (23 / 512), (47 / 256)]
def t80 : Tree (Fin 3) := .node 0 t72 t74
theorem cert80 : Certified t80 ({(1, false), (2, false)}) w80 := by
  apply certified_node cert72 cert74 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w72, w74, w80]

def w81 : Fin 8 → ℝ := ![(101 / 128), 0, (11 / 512), (13 / 256), (13 / 512), (5 / 512), (11 / 512), (21 / 256)]
def t81 : Tree (Fin 3) := .node 1 t0 t68
theorem cert81 : Certified t81 ({(0, true), (2, true)}) w81 := by
  apply certified_node cert0 cert68 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w68, w81]

def w82 : Fin 8 → ℝ := ![(101 / 128), (1 / 512), (5 / 256), (13 / 256), (13 / 512), (9 / 512), (7 / 512), (21 / 256)]
def t82 : Tree (Fin 3) := .node 2 t0 t67
theorem cert82 : Certified t82 ({(0, true), (1, true)}) w82 := by
  apply certified_node cert0 cert67 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w67, w82]

def w83 : Fin 8 → ℝ := ![(315 / 512), 0, (3 / 64), (33 / 512), (23 / 512), (5 / 128), (11 / 256), (75 / 512)]
def t83 : Tree (Fin 3) := .node 2 t70 t69
theorem cert83 : Certified t83 ({(0, true), (1, false)}) w83 := by
  apply certified_node cert70 cert69 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w70, w69, w83]

def w84 : Fin 8 → ℝ := ![(315 / 512), 0, (9 / 256), (15 / 512), (29 / 512), (9 / 128), (3 / 64), (75 / 512)]
def t84 : Tree (Fin 3) := .node 1 t66 t76
theorem cert84 : Certified t84 ({(0, false), (2, true)}) w84 := by
  apply certified_node cert66 cert76 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w66, w76, w84]

def w85 : Fin 8 → ℝ := ![(67 / 128), 0, (27 / 512), (55 / 512), (29 / 512), (1 / 32), (23 / 512), (47 / 256)]
def t85 : Tree (Fin 3) := .node 1 t75 t69
theorem cert85 : Certified t85 ({(0, false), (2, false)}) w85 := by
  apply certified_node cert75 cert69 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w75, w69, w85]

def w86 : Fin 8 → ℝ := ![(315 / 512), 0, (9 / 256), (15 / 512), (29 / 512), (19 / 256), (11 / 256), (75 / 512)]
def t86 : Tree (Fin 3) := .node 2 t66 t74
theorem cert86 : Certified t86 ({(0, false), (1, true)}) w86 := by
  apply certified_node cert66 cert74 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w66, w74, w86]

def w87 : Fin 8 → ℝ := ![(67 / 128), 0, (27 / 512), (55 / 512), (29 / 512), (15 / 512), (3 / 64), (47 / 256)]
def t87 : Tree (Fin 3) := .node 2 t73 t69
theorem cert87 : Certified t87 ({(0, false), (1, false)}) w87 := by
  apply certified_node cert73 cert69 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w73, w69, w87]

def w88 : Fin 8 → ℝ := ![(827 / 1024), 0, (9 / 512), (15 / 1024), (29 / 1024), (9 / 256), (3 / 128), (75 / 1024)]
def t88 : Tree (Fin 3) := .node 0 t0 t84
theorem cert88 : Certified t88 ({(1, true), (2, true)}) w88 := by
  apply certified_node cert0 cert84 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w84, w88]

def w89 : Fin 8 → ℝ := ![(21 / 32), (1 / 1024), (37 / 1024), (81 / 1024), (21 / 512), (25 / 1024), (15 / 512), (17 / 128)]
def t89 : Tree (Fin 3) := .node 0 t82 t85
theorem cert89 : Certified t89 ({(1, true), (2, false)}) w89 := by
  apply certified_node cert82 cert85 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w82, w85, w89]

def w90 : Fin 8 → ℝ := ![(21 / 32), 0, (19 / 512), (81 / 1024), (21 / 512), (5 / 256), (35 / 1024), (17 / 128)]
def t90 : Tree (Fin 3) := .node 0 t81 t87
theorem cert90 : Certified t90 ({(1, false), (2, true)}) w90 := by
  apply certified_node cert81 cert87 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w81, w87, w90]

def w91 : Fin 8 → ℝ := ![(583 / 1024), 0, (51 / 1024), (11 / 128), (13 / 256), (9 / 256), (45 / 1024), (169 / 1024)]
def t91 : Tree (Fin 3) := .node 0 t83 t85
theorem cert91 : Certified t91 ({(1, false), (2, false)}) w91 := by
  apply certified_node cert83 cert85 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w83, w85, w91]

def w92 : Fin 8 → ℝ := ![(827 / 1024), 0, (5 / 256), (15 / 1024), (27 / 1024), (9 / 256), (3 / 128), (75 / 1024)]
def t92 : Tree (Fin 3) := .node 1 t0 t79
theorem cert92 : Certified t92 ({(0, true), (2, true)}) w92 := by
  apply certified_node cert0 cert79 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w79, w92]

def w93 : Fin 8 → ℝ := ![(827 / 1024), (1 / 512), (9 / 512), (15 / 1024), (27 / 1024), (11 / 256), (1 / 64), (75 / 1024)]
def t93 : Tree (Fin 3) := .node 2 t0 t78
theorem cert93 : Certified t93 ({(0, true), (1, true)}) w93 := by
  apply certified_node cert0 cert78 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w78, w93]

def w94 : Fin 8 → ℝ := ![(21 / 32), 0, (35 / 1024), (13 / 256), (45 / 1024), (25 / 512), (17 / 512), (17 / 128)]
def t94 : Tree (Fin 3) := .node 2 t81 t80
theorem cert94 : Certified t94 ({(0, true), (1, false)}) w94 := by
  apply certified_node cert81 cert80 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w81, w80, w94]

def w95 : Fin 8 → ℝ := ![(21 / 32), 0, (37 / 1024), (81 / 1024), (43 / 1024), (5 / 256), (35 / 1024), (17 / 128)]
def t95 : Tree (Fin 3) := .node 1 t77 t87
theorem cert95 : Certified t95 ({(0, false), (2, true)}) w95 := by
  apply certified_node cert77 cert87 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w77, w87, w95]

def w96 : Fin 8 → ℝ := ![(583 / 1024), 0, (21 / 512), (41 / 1024), (61 / 1024), (83 / 1024), (45 / 1024), (169 / 1024)]
def t96 : Tree (Fin 3) := .node 1 t86 t80
theorem cert96 : Certified t96 ({(0, false), (2, false)}) w96 := by
  apply certified_node cert86 cert80 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w86, w80, w96]

def w97 : Fin 8 → ℝ := ![(21 / 32), 0, (37 / 1024), (81 / 1024), (43 / 1024), (21 / 1024), (17 / 512), (17 / 128)]
def t97 : Tree (Fin 3) := .node 2 t77 t85
theorem cert97 : Certified t97 ({(0, false), (1, true)}) w97 := by
  apply certified_node cert77 cert85 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w77, w85, w97]

def w98 : Fin 8 → ℝ := ![(583 / 1024), 0, (21 / 512), (41 / 1024), (61 / 1024), (81 / 1024), (47 / 1024), (169 / 1024)]
def t98 : Tree (Fin 3) := .node 2 t84 t80
theorem cert98 : Certified t98 ({(0, false), (1, false)}) w98 := by
  apply certified_node cert84 cert80 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w84, w80, w98]

def w99 : Fin 8 → ℝ := ![(53 / 64), 0, (37 / 2048), (81 / 2048), (43 / 2048), (5 / 512), (35 / 2048), (17 / 256)]
def t99 : Tree (Fin 3) := .node 0 t0 t95
theorem cert99 : Certified t99 ({(1, true), (2, true)}) w99 := by
  apply certified_node cert0 cert95 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w95, w99]

def w100 : Fin 8 → ℝ := ![(705 / 1024), (1 / 1024), (15 / 512), (7 / 256), (11 / 256), (127 / 2048), (61 / 2048), (61 / 512)]
def t100 : Tree (Fin 3) := .node 0 t93 t96
theorem cert100 : Certified t100 ({(1, true), (2, false)}) w100 := by
  apply certified_node cert93 cert96 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w93, w96, w100]

def w101 : Fin 8 → ℝ := ![(705 / 1024), 0, (31 / 1024), (7 / 256), (11 / 256), (117 / 2048), (71 / 2048), (61 / 512)]
def t101 : Tree (Fin 3) := .node 0 t92 t98
theorem cert101 : Certified t101 ({(1, false), (2, true)}) w101 := by
  apply certified_node cert92 cert98 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w92, w98, w101]

def w102 : Fin 8 → ℝ := ![(1255 / 2048), 0, (77 / 2048), (93 / 2048), (53 / 1024), (133 / 2048), (79 / 2048), (305 / 2048)]
def t102 : Tree (Fin 3) := .node 0 t94 t96
theorem cert102 : Certified t102 ({(1, false), (2, false)}) w102 := by
  apply certified_node cert94 cert96 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w94, w96, w102]

def w103 : Fin 8 → ℝ := ![(53 / 64), 0, (19 / 1024), (81 / 2048), (21 / 1024), (5 / 512), (35 / 2048), (17 / 256)]
def t103 : Tree (Fin 3) := .node 1 t0 t90
theorem cert103 : Certified t103 ({(0, true), (2, true)}) w103 := by
  apply certified_node cert0 cert90 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w90, w103]

def w104 : Fin 8 → ℝ := ![(53 / 64), (1 / 2048), (37 / 2048), (81 / 2048), (21 / 1024), (25 / 2048), (15 / 1024), (17 / 256)]
def t104 : Tree (Fin 3) := .node 2 t0 t89
theorem cert104 : Certified t104 ({(0, true), (1, true)}) w104 := by
  apply certified_node cert0 cert89 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w89, w104]

def w105 : Fin 8 → ℝ := ![(705 / 1024), 0, (71 / 2048), (103 / 2048), (79 / 2048), (9 / 256), (69 / 2048), (61 / 512)]
def t105 : Tree (Fin 3) := .node 2 t92 t91
theorem cert105 : Certified t105 ({(0, true), (1, false)}) w105 := by
  apply certified_node cert92 cert91 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w92, w91, w105]

def w106 : Fin 8 → ℝ := ![(705 / 1024), 0, (15 / 512), (7 / 256), (45 / 1024), (117 / 2048), (71 / 2048), (61 / 512)]
def t106 : Tree (Fin 3) := .node 1 t88 t98
theorem cert106 : Certified t106 ({(0, false), (2, true)}) w106 := by
  apply certified_node cert88 cert98 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w88, w98, w106]

def w107 : Fin 8 → ℝ := ![(1255 / 2048), 0, (11 / 256), (169 / 2048), (95 / 2048), (57 / 2048), (79 / 2048), (305 / 2048)]
def t107 : Tree (Fin 3) := .node 1 t97 t91
theorem cert107 : Certified t107 ({(0, false), (2, false)}) w107 := by
  apply certified_node cert97 cert91 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w97, w91, w107]

def w108 : Fin 8 → ℝ := ![(705 / 1024), 0, (15 / 512), (7 / 256), (45 / 1024), (119 / 2048), (69 / 2048), (61 / 512)]
def t108 : Tree (Fin 3) := .node 2 t88 t96
theorem cert108 : Certified t108 ({(0, false), (1, true)}) w108 := by
  apply certified_node cert88 cert96 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w88, w96, w108]

def w109 : Fin 8 → ℝ := ![(1255 / 2048), 0, (11 / 256), (169 / 2048), (95 / 2048), (7 / 256), (5 / 128), (305 / 2048)]
def t109 : Tree (Fin 3) := .node 2 t95 t91
theorem cert109 : Certified t109 ({(0, false), (1, false)}) w109 := by
  apply certified_node cert95 cert91 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w95, w91, w109]

def w110 : Fin 8 → ℝ := ![(1729 / 2048), 0, (15 / 1024), (7 / 512), (45 / 2048), (117 / 4096), (71 / 4096), (61 / 1024)]
def t110 : Tree (Fin 3) := .node 0 t0 t106
theorem cert110 : Certified t110 ({(1, true), (2, true)}) w110 := by
  apply certified_node cert0 cert106 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w106, w110]

def w111 : Fin 8 → ℝ := ![(2951 / 4096), (1 / 4096), (125 / 4096), (125 / 2048), (137 / 4096), (41 / 2048), (109 / 4096), (441 / 4096)]
def t111 : Tree (Fin 3) := .node 0 t104 t107
theorem cert111 : Certified t111 ({(1, true), (2, false)}) w111 := by
  apply certified_node cert104 cert107 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w104, w107, w111]

def w112 : Fin 8 → ℝ := ![(2951 / 4096), 0, (63 / 2048), (125 / 2048), (137 / 4096), (19 / 1024), (115 / 4096), (441 / 4096)]
def t112 : Tree (Fin 3) := .node 0 t103 t109
theorem cert112 : Certified t112 ({(1, false), (2, true)}) w112 := by
  apply certified_node cert103 cert109 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w103, w109, w112]

def w113 : Fin 8 → ℝ := ![(2665 / 4096), 0, (159 / 4096), (17 / 256), (87 / 2048), (129 / 4096), (37 / 1024), (549 / 4096)]
def t113 : Tree (Fin 3) := .node 0 t105 t107
theorem cert113 : Certified t113 ({(1, false), (2, false)}) w113 := by
  apply certified_node cert105 cert107 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w105, w107, w113]

def w114 : Fin 8 → ℝ := ![(1729 / 2048), 0, (31 / 2048), (7 / 512), (11 / 512), (117 / 4096), (71 / 4096), (61 / 1024)]
def t114 : Tree (Fin 3) := .node 1 t0 t101
theorem cert114 : Certified t114 ({(0, true), (2, true)}) w114 := by
  apply certified_node cert0 cert101 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w101, w114]

def w115 : Fin 8 → ℝ := ![(1729 / 2048), (1 / 2048), (15 / 1024), (7 / 512), (11 / 512), (127 / 4096), (61 / 4096), (61 / 1024)]
def t115 : Tree (Fin 3) := .node 2 t0 t100
theorem cert115 : Certified t115 ({(0, true), (1, true)}) w115 := by
  apply certified_node cert0 cert100 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w100, w115]

def w116 : Fin 8 → ℝ := ![(2951 / 4096), 0, (115 / 4096), (87 / 2048), (37 / 1024), (153 / 4096), (57 / 2048), (441 / 4096)]
def t116 : Tree (Fin 3) := .node 2 t103 t102
theorem cert116 : Certified t116 ({(0, true), (1, false)}) w116 := by
  apply certified_node cert103 cert102 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w103, w102, w116]

def w117 : Fin 8 → ℝ := ![(2951 / 4096), 0, (125 / 4096), (125 / 2048), (69 / 2048), (19 / 1024), (115 / 4096), (441 / 4096)]
def t117 : Tree (Fin 3) := .node 1 t99 t109
theorem cert117 : Certified t117 ({(0, false), (2, true)}) w117 := by
  apply certified_node cert99 cert109 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w99, w109, w117]

def w118 : Fin 8 → ℝ := ![(2665 / 4096), 0, (137 / 4096), (149 / 4096), (49 / 1024), (63 / 1024), (37 / 1024), (549 / 4096)]
def t118 : Tree (Fin 3) := .node 1 t108 t102
theorem cert118 : Certified t118 ({(0, false), (2, false)}) w118 := by
  apply certified_node cert108 cert102 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w108, w102, w118]

def w119 : Fin 8 → ℝ := ![(2951 / 4096), 0, (125 / 4096), (125 / 2048), (69 / 2048), (77 / 4096), (57 / 2048), (441 / 4096)]
def t119 : Tree (Fin 3) := .node 2 t99 t107
theorem cert119 : Certified t119 ({(0, false), (1, true)}) w119 := by
  apply certified_node cert99 cert107 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w99, w107, w119]

def w120 : Fin 8 → ℝ := ![(2665 / 4096), 0, (137 / 4096), (149 / 4096), (49 / 1024), (125 / 2048), (75 / 2048), (549 / 4096)]
def t120 : Tree (Fin 3) := .node 2 t106 t102
theorem cert120 : Certified t120 ({(0, false), (1, false)}) w120 := by
  apply certified_node cert106 cert102 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w106, w102, w120]

def w121 : Fin 8 → ℝ := ![(7047 / 8192), 0, (125 / 8192), (125 / 4096), (69 / 4096), (19 / 2048), (115 / 8192), (441 / 8192)]
def t121 : Tree (Fin 3) := .node 0 t0 t117
theorem cert121 : Certified t121 ({(1, true), (2, true)}) w121 := by
  apply certified_node cert0 cert117 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w117, w121]

def w122 : Fin 8 → ℝ := ![(6123 / 8192), (1 / 4096), (197 / 8192), (205 / 8192), (71 / 2048), (379 / 8192), (209 / 8192), (793 / 8192)]
def t122 : Tree (Fin 3) := .node 0 t115 t118
theorem cert122 : Certified t122 ({(1, true), (2, false)}) w122 := by
  apply certified_node cert115 cert118 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w115, w118, w122]

def w123 : Fin 8 → ℝ := ![(6123 / 8192), 0, (199 / 8192), (205 / 8192), (71 / 2048), (367 / 8192), (221 / 8192), (793 / 8192)]
def t123 : Tree (Fin 3) := .node 0 t114 t120
theorem cert123 : Certified t123 ({(1, false), (2, true)}) w123 := by
  apply certified_node cert114 cert120 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w114, w120, w123]

def w124 : Fin 8 → ℝ := ![(351 / 512), 0, (63 / 2048), (323 / 8192), (43 / 1024), (405 / 8192), (131 / 4096), (495 / 4096)]
def t124 : Tree (Fin 3) := .node 0 t116 t118
theorem cert124 : Certified t124 ({(1, false), (2, false)}) w124 := by
  apply certified_node cert116 cert118 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w116, w118, w124]

def w125 : Fin 8 → ℝ := ![(7047 / 8192), 0, (63 / 4096), (125 / 4096), (137 / 8192), (19 / 2048), (115 / 8192), (441 / 8192)]
def t125 : Tree (Fin 3) := .node 1 t0 t112
theorem cert125 : Certified t125 ({(0, true), (2, true)}) w125 := by
  apply certified_node cert0 cert112 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w112, w125]

def w126 : Fin 8 → ℝ := ![(7047 / 8192), (1 / 8192), (125 / 8192), (125 / 4096), (137 / 8192), (41 / 4096), (109 / 8192), (441 / 8192)]
def t126 : Tree (Fin 3) := .node 2 t0 t111
theorem cert126 : Certified t126 ({(0, true), (1, true)}) w126 := by
  apply certified_node cert0 cert111 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w111, w126]

def w127 : Fin 8 → ℝ := ![(6123 / 8192), 0, (221 / 8192), (41 / 1024), (131 / 4096), (123 / 4096), (219 / 8192), (793 / 8192)]
def t127 : Tree (Fin 3) := .node 2 t114 t113
theorem cert127 : Certified t127 ({(0, true), (1, false)}) w127 := by
  apply certified_node cert114 cert113 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w114, w113, w127]

def w128 : Fin 8 → ℝ := ![(6123 / 8192), 0, (197 / 8192), (205 / 8192), (143 / 4096), (367 / 8192), (221 / 8192), (793 / 8192)]
def t128 : Tree (Fin 3) := .node 1 t110 t120
theorem cert128 : Certified t128 ({(0, false), (2, true)}) w128 := by
  apply certified_node cert110 cert120 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w110, w120, w128]

def w129 : Fin 8 → ℝ := ![(351 / 512), 0, (71 / 2048), (261 / 4096), (39 / 1024), (103 / 4096), (131 / 4096), (495 / 4096)]
def t129 : Tree (Fin 3) := .node 1 t119 t113
theorem cert129 : Certified t129 ({(0, false), (2, false)}) w129 := by
  apply certified_node cert119 cert113 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w119, w113, w129]

def w130 : Fin 8 → ℝ := ![(6123 / 8192), 0, (197 / 8192), (205 / 8192), (143 / 4096), (369 / 8192), (219 / 8192), (793 / 8192)]
def t130 : Tree (Fin 3) := .node 2 t110 t118
theorem cert130 : Certified t130 ({(0, false), (1, true)}) w130 := by
  apply certified_node cert110 cert118 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w110, w118, w130]

def w131 : Fin 8 → ℝ := ![(351 / 512), 0, (71 / 2048), (261 / 4096), (39 / 1024), (205 / 8192), (263 / 8192), (495 / 4096)]
def t131 : Tree (Fin 3) := .node 2 t117 t113
theorem cert131 : Certified t131 ({(0, false), (1, false)}) w131 := by
  apply certified_node cert117 cert113 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w117, w113, w131]

def w132 : Fin 8 → ℝ := ![(14315 / 16384), 0, (197 / 16384), (205 / 16384), (143 / 8192), (367 / 16384), (221 / 16384), (793 / 16384)]
def t132 : Tree (Fin 3) := .node 0 t0 t128
theorem cert132 : Certified t132 ({(1, true), (2, true)}) w132 := by
  apply certified_node cert0 cert128 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w128, w132]

def w133 : Fin 8 → ℝ := ![(12663 / 16384), (1 / 16384), (409 / 16384), (193 / 4096), (449 / 16384), (9 / 512), (371 / 16384), (1431 / 16384)]
def t133 : Tree (Fin 3) := .node 0 t126 t129
theorem cert133 : Certified t133 ({(1, true), (2, false)}) w133 := by
  apply certified_node cert126 cert129 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w126, w129, w133]

def w134 : Fin 8 → ℝ := ![(12663 / 16384), 0, (205 / 8192), (193 / 4096), (449 / 16384), (281 / 16384), (189 / 8192), (1431 / 16384)]
def t134 : Tree (Fin 3) := .node 0 t125 t131
theorem cert134 : Certified t134 ({(1, false), (2, true)}) w134 := by
  apply certified_node cert125 cert131 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w125, w131, w134]

def w135 : Fin 8 → ℝ := ![(11739 / 16384), 0, (505 / 16384), (425 / 8192), (287 / 8192), (113 / 4096), (481 / 16384), (1783 / 16384)]
def t135 : Tree (Fin 3) := .node 0 t127 t129
theorem cert135 : Certified t135 ({(1, false), (2, false)}) w135 := by
  apply certified_node cert127 cert129 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w127, w129, w135]

def w136 : Fin 8 → ℝ := ![(14315 / 16384), 0, (199 / 16384), (205 / 16384), (71 / 4096), (367 / 16384), (221 / 16384), (793 / 16384)]
def t136 : Tree (Fin 3) := .node 1 t0 t123
theorem cert136 : Certified t136 ({(0, true), (2, true)}) w136 := by
  apply certified_node cert0 cert123 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w123, w136]

def w137 : Fin 8 → ℝ := ![(14315 / 16384), (1 / 8192), (197 / 16384), (205 / 16384), (71 / 4096), (379 / 16384), (209 / 16384), (793 / 16384)]
def t137 : Tree (Fin 3) := .node 2 t0 t122
theorem cert137 : Certified t137 ({(0, true), (1, true)}) w137 := by
  apply certified_node cert0 cert122 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w122, w137]

def w138 : Fin 8 → ℝ := ![(12663 / 16384), 0, (189 / 8192), (573 / 16384), (481 / 16384), (481 / 16384), (377 / 16384), (1431 / 16384)]
def t138 : Tree (Fin 3) := .node 2 t125 t124
theorem cert138 : Certified t138 ({(0, true), (1, false)}) w138 := by
  apply certified_node cert125 cert124 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w125, w124, w138]

def w139 : Fin 8 → ℝ := ![(12663 / 16384), 0, (409 / 16384), (193 / 4096), (225 / 8192), (281 / 16384), (189 / 8192), (1431 / 16384)]
def t139 : Tree (Fin 3) := .node 1 t121 t131
theorem cert139 : Certified t139 ({(0, false), (2, true)}) w139 := by
  apply certified_node cert121 cert131 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w121, w131, w139]

def w140 : Fin 8 → ℝ := ![(11739 / 16384), 0, (449 / 16384), (33 / 1024), (315 / 8192), (387 / 8192), (481 / 16384), (1783 / 16384)]
def t140 : Tree (Fin 3) := .node 1 t130 t124
theorem cert140 : Certified t140 ({(0, false), (2, false)}) w140 := by
  apply certified_node cert130 cert124 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w130, w124, w140]

def w141 : Fin 8 → ℝ := ![(12663 / 16384), 0, (409 / 16384), (193 / 4096), (225 / 8192), (141 / 8192), (377 / 16384), (1431 / 16384)]
def t141 : Tree (Fin 3) := .node 2 t121 t129
theorem cert141 : Certified t141 ({(0, false), (1, true)}) w141 := by
  apply certified_node cert121 cert129 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w121, w129, w141]

def w142 : Fin 8 → ℝ := ![(11739 / 16384), 0, (449 / 16384), (33 / 1024), (315 / 8192), (193 / 4096), (483 / 16384), (1783 / 16384)]
def t142 : Tree (Fin 3) := .node 2 t128 t124
theorem cert142 : Certified t142 ({(0, false), (1, false)}) w142 := by
  apply certified_node cert128 cert124 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w128, w124, w142]

def w143 : Fin 8 → ℝ := ![(29047 / 32768), 0, (409 / 32768), (193 / 8192), (225 / 16384), (281 / 32768), (189 / 16384), (1431 / 32768)]
def t143 : Tree (Fin 3) := .node 0 t0 t139
theorem cert143 : Certified t143 ({(1, true), (2, true)}) w143 := by
  apply certified_node cert0 cert139 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w139, w143]

def w144 : Fin 8 → ℝ := ![(13027 / 16384), (1 / 16384), (323 / 16384), (733 / 32768), (457 / 16384), (1153 / 32768), (345 / 16384), (161 / 2048)]
def t144 : Tree (Fin 3) := .node 0 t137 t140
theorem cert144 : Certified t144 ({(1, true), (2, false)}) w144 := by
  apply certified_node cert137 cert140 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w137, w140, w144]

def w145 : Fin 8 → ℝ := ![(13027 / 16384), 0, (81 / 4096), (733 / 32768), (457 / 16384), (1139 / 32768), (11 / 512), (161 / 2048)]
def t145 : Tree (Fin 3) := .node 0 t136 t142
theorem cert145 : Certified t145 ({(1, false), (2, true)}) w145 := by
  apply certified_node cert136 cert142 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w136, w142, w145]

def w146 : Fin 8 → ℝ := ![(12201 / 16384), 0, (827 / 32768), (1101 / 32768), (1111 / 32768), (1255 / 32768), (429 / 16384), (1607 / 16384)]
def t146 : Tree (Fin 3) := .node 0 t138 t140
theorem cert146 : Certified t146 ({(1, false), (2, false)}) w146 := by
  apply certified_node cert138 cert140 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w138, w140, w146]

def w147 : Fin 8 → ℝ := ![(29047 / 32768), 0, (205 / 16384), (193 / 8192), (449 / 32768), (281 / 32768), (189 / 16384), (1431 / 32768)]
def t147 : Tree (Fin 3) := .node 1 t0 t134
theorem cert147 : Certified t147 ({(0, true), (2, true)}) w147 := by
  apply certified_node cert0 cert134 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w134, w147]

def w148 : Fin 8 → ℝ := ![(29047 / 32768), (1 / 32768), (409 / 32768), (193 / 8192), (449 / 32768), (9 / 1024), (371 / 32768), (1431 / 32768)]
def t148 : Tree (Fin 3) := .node 2 t0 t133
theorem cert148 : Certified t148 ({(0, true), (1, true)}) w148 := by
  apply certified_node cert0 cert133 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w133, w148]

def w149 : Fin 8 → ℝ := ![(13027 / 16384), 0, (11 / 512), (1055 / 32768), (429 / 16384), (819 / 32768), (351 / 16384), (161 / 2048)]
def t149 : Tree (Fin 3) := .node 2 t136 t135
theorem cert149 : Certified t149 ({(0, true), (1, false)}) w149 := by
  apply certified_node cert136 cert135 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w136, w135, w149]

def w150 : Fin 8 → ℝ := ![(13027 / 16384), 0, (323 / 16384), (733 / 32768), (229 / 8192), (1139 / 32768), (11 / 512), (161 / 2048)]
def t150 : Tree (Fin 3) := .node 1 t132 t142
theorem cert150 : Certified t150 ({(0, false), (2, true)}) w150 := by
  apply certified_node cert132 cert142 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w132, w142, w150]

def w151 : Fin 8 → ℝ := ![(12201 / 16384), 0, (457 / 16384), (811 / 16384), (1 / 32), (367 / 16384), (429 / 16384), (1607 / 16384)]
def t151 : Tree (Fin 3) := .node 1 t141 t135
theorem cert151 : Certified t151 ({(0, false), (2, false)}) w151 := by
  apply certified_node cert141 cert135 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w141, w135, w151]

def w152 : Fin 8 → ℝ := ![(13027 / 16384), 0, (323 / 16384), (733 / 32768), (229 / 8192), (1141 / 32768), (351 / 16384), (161 / 2048)]
def t152 : Tree (Fin 3) := .node 2 t132 t140
theorem cert152 : Certified t152 ({(0, false), (1, true)}) w152 := by
  apply certified_node cert132 cert140 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w132, w140, w152]

def w153 : Fin 8 → ℝ := ![(12201 / 16384), 0, (457 / 16384), (811 / 16384), (1 / 32), (733 / 32768), (859 / 32768), (1607 / 16384)]
def t153 : Tree (Fin 3) := .node 2 t139 t135
theorem cert153 : Certified t153 ({(0, false), (1, false)}) w153 := by
  apply certified_node cert139 cert135 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w139, w135, w153]

def w154 : Fin 8 → ℝ := ![(29411 / 32768), 0, (323 / 32768), (733 / 65536), (229 / 16384), (1139 / 65536), (11 / 1024), (161 / 4096)]
def t154 : Tree (Fin 3) := .node 0 t0 t150
theorem cert154 : Certified t154 ({(1, true), (2, true)}) w154 := by
  apply certified_node cert0 cert150 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w150, w154]

def w155 : Fin 8 → ℝ := ![(53449 / 65536), (1 / 65536), (1323 / 65536), (1197 / 32768), (1473 / 65536), (511 / 32768), (1229 / 65536), (4645 / 65536)]
def t155 : Tree (Fin 3) := .node 0 t148 t151
theorem cert155 : Certified t155 ({(1, true), (2, false)}) w155 := by
  apply certified_node cert148 cert151 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w148, w151, w155]

def w156 : Fin 8 → ℝ := ![(53449 / 65536), 0, (331 / 16384), (1197 / 32768), (1473 / 65536), (507 / 32768), (1237 / 65536), (4645 / 65536)]
def t156 : Tree (Fin 3) := .node 0 t147 t153
theorem cert156 : Certified t156 ({(1, false), (2, true)}) w156 := by
  apply certified_node cert147 cert153 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w147, w153, w156]

def w157 : Fin 8 → ℝ := ![(6307 / 8192), 0, (809 / 32768), (2677 / 65536), (941 / 32768), (1553 / 65536), (195 / 8192), (2895 / 32768)]
def t157 : Tree (Fin 3) := .node 0 t149 t151
theorem cert157 : Certified t157 ({(1, false), (2, false)}) w157 := by
  apply certified_node cert149 cert151 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w149, w151, w157]

def w158 : Fin 8 → ℝ := ![(29411 / 32768), 0, (81 / 8192), (733 / 65536), (457 / 32768), (1139 / 65536), (11 / 1024), (161 / 4096)]
def t158 : Tree (Fin 3) := .node 1 t0 t145
theorem cert158 : Certified t158 ({(0, true), (2, true)}) w158 := by
  apply certified_node cert0 cert145 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w145, w158]

def w159 : Fin 8 → ℝ := ![(29411 / 32768), (1 / 32768), (323 / 32768), (733 / 65536), (457 / 32768), (1153 / 65536), (345 / 32768), (161 / 4096)]
def t159 : Tree (Fin 3) := .node 2 t0 t144
theorem cert159 : Certified t159 ({(0, true), (1, true)}) w159 := by
  apply certified_node cert0 cert144 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w144, w159]

def w160 : Fin 8 → ℝ := ![(53449 / 65536), 0, (1237 / 65536), (1873 / 65536), (195 / 8192), (3 / 128), (309 / 16384), (4645 / 65536)]
def t160 : Tree (Fin 3) := .node 2 t147 t146
theorem cert160 : Certified t160 ({(0, true), (1, false)}) w160 := by
  apply certified_node cert147 cert146 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w147, w146, w160]

def w161 : Fin 8 → ℝ := ![(53449 / 65536), 0, (1323 / 65536), (1197 / 32768), (737 / 32768), (507 / 32768), (1237 / 65536), (4645 / 65536)]
def t161 : Tree (Fin 3) := .node 1 t143 t153
theorem cert161 : Certified t161 ({(0, false), (2, true)}) w161 := by
  apply certified_node cert143 cert153 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w143, w153, w161]

def w162 : Fin 8 → ℝ := ![(6307 / 8192), 0, (1473 / 65536), (917 / 32768), (2027 / 65536), (599 / 16384), (195 / 8192), (2895 / 32768)]
def t162 : Tree (Fin 3) := .node 1 t152 t146
theorem cert162 : Certified t162 ({(0, false), (2, false)}) w162 := by
  apply certified_node cert152 cert146 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w152, w146, w162]

def w163 : Fin 8 → ℝ := ![(53449 / 65536), 0, (1323 / 65536), (1197 / 32768), (737 / 32768), (1015 / 65536), (309 / 16384), (4645 / 65536)]
def t163 : Tree (Fin 3) := .node 2 t143 t151
theorem cert163 : Certified t163 ({(0, false), (1, true)}) w163 := by
  apply certified_node cert143 cert151 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w143, w151, w163]

def w164 : Fin 8 → ℝ := ![(6307 / 8192), 0, (1473 / 65536), (917 / 32768), (2027 / 65536), (1197 / 32768), (781 / 32768), (2895 / 32768)]
def t164 : Tree (Fin 3) := .node 2 t150 t146
theorem cert164 : Certified t164 ({(0, false), (1, false)}) w164 := by
  apply certified_node cert150 cert146 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w150, w146, w164]

def w165 : Fin 8 → ℝ := ![(118985 / 131072), 0, (1323 / 131072), (1197 / 65536), (737 / 65536), (507 / 65536), (1237 / 131072), (4645 / 131072)]
def t165 : Tree (Fin 3) := .node 0 t0 t161
theorem cert165 : Certified t165 ({(1, true), (2, true)}) w165 := by
  apply certified_node cert0 cert161 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w161, w165]

def w166 : Fin 8 → ℝ := ![(54639 / 65536), (1 / 65536), (2119 / 131072), (2567 / 131072), (2941 / 131072), (3549 / 131072), (1125 / 65536), (4183 / 65536)]
def t166 : Tree (Fin 3) := .node 0 t159 t162
theorem cert166 : Certified t166 ({(1, true), (2, false)}) w166 := by
  apply certified_node cert159 cert162 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w159, w162, w166]

def w167 : Fin 8 → ℝ := ![(54639 / 65536), 0, (2121 / 131072), (2567 / 131072), (2941 / 131072), (3533 / 131072), (1133 / 65536), (4183 / 65536)]
def t167 : Tree (Fin 3) := .node 0 t158 t164
theorem cert167 : Certified t167 ({(1, false), (2, true)}) w167 := by
  apply certified_node cert158 cert164 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w158, w164, w167]

def w168 : Fin 8 → ℝ := ![(103905 / 131072), 0, (1355 / 65536), (3707 / 131072), (3587 / 131072), (983 / 32768), (699 / 32768), (10435 / 131072)]
def t168 : Tree (Fin 3) := .node 0 t160 t162
theorem cert168 : Certified t168 ({(1, false), (2, false)}) w168 := by
  apply certified_node cert160 cert162 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w160, w162, w168]

def w169 : Fin 8 → ℝ := ![(118985 / 131072), 0, (331 / 32768), (1197 / 65536), (1473 / 131072), (507 / 65536), (1237 / 131072), (4645 / 131072)]
def t169 : Tree (Fin 3) := .node 1 t0 t156
theorem cert169 : Certified t169 ({(0, true), (2, true)}) w169 := by
  apply certified_node cert0 cert156 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w156, w169]

def w170 : Fin 8 → ℝ := ![(118985 / 131072), (1 / 131072), (1323 / 131072), (1197 / 65536), (1473 / 131072), (511 / 65536), (1229 / 131072), (4645 / 131072)]
def t170 : Tree (Fin 3) := .node 2 t0 t155
theorem cert170 : Certified t170 ({(0, true), (1, true)}) w170 := by
  apply certified_node cert0 cert155 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w155, w170]

def w171 : Fin 8 → ℝ := ![(54639 / 65536), 0, (1133 / 65536), (1705 / 65536), (699 / 32768), (673 / 32768), (283 / 16384), (4183 / 65536)]
def t171 : Tree (Fin 3) := .node 2 t158 t157
theorem cert171 : Certified t171 ({(0, true), (1, false)}) w171 := by
  apply certified_node cert158 cert157 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w158, w157, w171]

def w172 : Fin 8 → ℝ := ![(54639 / 65536), 0, (2119 / 131072), (2567 / 131072), (2943 / 131072), (3533 / 131072), (1133 / 65536), (4183 / 65536)]
def t172 : Tree (Fin 3) := .node 1 t154 t164
theorem cert172 : Certified t172 ({(0, false), (2, true)}) w172 := by
  apply certified_node cert154 cert164 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w154, w164, w172]

def w173 : Fin 8 → ℝ := ![(103905 / 131072), 0, (2941 / 131072), (5071 / 131072), (839 / 32768), (321 / 16384), (699 / 32768), (10435 / 131072)]
def t173 : Tree (Fin 3) := .node 1 t163 t157
theorem cert173 : Certified t173 ({(0, false), (2, false)}) w173 := by
  apply certified_node cert163 cert157 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w163, w157, w173]

def w174 : Fin 8 → ℝ := ![(54639 / 65536), 0, (2119 / 131072), (2567 / 131072), (2943 / 131072), (3535 / 131072), (283 / 16384), (4183 / 65536)]
def t174 : Tree (Fin 3) := .node 2 t154 t162
theorem cert174 : Certified t174 ({(0, false), (1, true)}) w174 := by
  apply certified_node cert154 cert162 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w154, w162, w174]

def w175 : Fin 8 → ℝ := ![(103905 / 131072), 0, (2941 / 131072), (5071 / 131072), (839 / 32768), (2567 / 131072), (2797 / 131072), (10435 / 131072)]
def t175 : Tree (Fin 3) := .node 2 t161 t157
theorem cert175 : Certified t175 ({(0, false), (1, false)}) w175 := by
  apply certified_node cert161 cert157 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w161, w157, w175]

def w176 : Fin 8 → ℝ := ![(120175 / 131072), 0, (2119 / 262144), (2567 / 262144), (2943 / 262144), (3533 / 262144), (1133 / 131072), (4183 / 131072)]
def t176 : Tree (Fin 3) := .node 0 t0 t172
theorem cert176 : Certified t176 ({(1, true), (2, true)}) w176 := by
  apply certified_node cert0 cert172 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w172, w176]

def w177 : Fin 8 → ℝ := ![(111445 / 131072), (1 / 262144), (533 / 32768), (7465 / 262144), (4829 / 262144), (1795 / 131072), (4025 / 262144), (1885 / 32768)]
def t177 : Tree (Fin 3) := .node 0 t170 t173
theorem cert177 : Certified t177 ({(1, true), (2, false)}) w177 := by
  apply certified_node cert170 cert173 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w170, w173, w177]

def w178 : Fin 8 → ℝ := ![(213183 / 262144), 0, (5207 / 262144), (8481 / 262144), (769 / 32768), (1315 / 65536), (1265 / 65536), (18801 / 262144)]
def t178 : Tree (Fin 3) := .node 0 t171 t173
theorem cert178 : Certified t178 ({(1, false), (2, false)}) w178 := by
  apply certified_node cert171 cert173 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w171, w173, w178]

def w179 : Fin 8 → ℝ := ![(120175 / 131072), 0, (2121 / 262144), (2567 / 262144), (2941 / 262144), (3533 / 262144), (1133 / 131072), (4183 / 131072)]
def t179 : Tree (Fin 3) := .node 1 t0 t167
theorem cert179 : Certified t179 ({(0, true), (2, true)}) w179 := by
  apply certified_node cert0 cert167 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w167, w179]

def w180 : Fin 8 → ℝ := ![(120175 / 131072), (1 / 131072), (2119 / 262144), (2567 / 262144), (2941 / 262144), (3549 / 262144), (1125 / 131072), (4183 / 131072)]
def t180 : Tree (Fin 3) := .node 2 t0 t166
theorem cert180 : Certified t180 ({(0, true), (1, true)}) w180 := by
  apply certified_node cert0 cert166 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w166, w180]

def w181 : Fin 8 → ℝ := ![(111445 / 131072), 0, (2017 / 131072), (6101 / 262144), (1265 / 65536), (2473 / 131072), (4033 / 262144), (1885 / 32768)]
def t181 : Tree (Fin 3) := .node 2 t169 t168
theorem cert181 : Certified t181 ({(0, true), (1, false)}) w181 := by
  apply certified_node cert169 cert168 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w169, w168, w181]

def w182 : Fin 8 → ℝ := ![(111445 / 131072), 0, (533 / 32768), (7465 / 262144), (2415 / 131072), (3581 / 262144), (2017 / 131072), (1885 / 32768)]
def t182 : Tree (Fin 3) := .node 1 t165 t175
theorem cert182 : Certified t182 ({(0, false), (2, true)}) w182 := by
  apply certified_node cert165 cert175 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w165, w175, w182]

def w183 : Fin 8 → ℝ := ![(213183 / 262144), 0, (4829 / 262144), (3137 / 131072), (3265 / 131072), (7467 / 262144), (1265 / 65536), (18801 / 262144)]
def t183 : Tree (Fin 3) := .node 1 t174 t168
theorem cert183 : Certified t183 ({(0, false), (2, false)}) w183 := by
  apply certified_node cert174 cert168 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w174, w168, w183]

def w184 : Fin 8 → ℝ := ![(111445 / 131072), 0, (533 / 32768), (7465 / 262144), (2415 / 131072), (1791 / 131072), (4033 / 262144), (1885 / 32768)]
def t184 : Tree (Fin 3) := .node 2 t165 t173
theorem cert184 : Certified t184 ({(0, false), (1, true)}) w184 := by
  apply certified_node cert165 cert173 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w165, w173, w184]

def w185 : Fin 8 → ℝ := ![(213183 / 262144), 0, (4829 / 262144), (3137 / 131072), (3265 / 131072), (7465 / 262144), (2531 / 131072), (18801 / 262144)]
def t185 : Tree (Fin 3) := .node 2 t172 t168
theorem cert185 : Certified t185 ({(0, false), (1, false)}) w185 := by
  apply certified_node cert172 cert168 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w172, w168, w185]

def w186 : Fin 8 → ℝ := ![(242517 / 262144), 0, (533 / 65536), (7465 / 524288), (2415 / 262144), (3581 / 524288), (2017 / 262144), (1885 / 65536)]
def t186 : Tree (Fin 3) := .node 0 t0 t182
theorem cert186 : Certified t186 ({(1, true), (2, true)}) w186 := by
  apply certified_node cert0 cert182 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w182, w186]

def w187 : Fin 8 → ℝ := ![(453533 / 524288), (1 / 262144), (1737 / 131072), (8841 / 524288), (9471 / 524288), (1377 / 65536), (3655 / 262144), (27167 / 524288)]
def t187 : Tree (Fin 3) := .node 0 t180 t183
theorem cert187 : Certified t187 ({(1, true), (2, false)}) w187 := by
  apply certified_node cert180 cert183 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w180, w183, w187]

def w188 : Fin 8 → ℝ := ![(453533 / 524288), 0, (3475 / 262144), (8841 / 524288), (9471 / 524288), (5499 / 262144), (229 / 16384), (27167 / 524288)]
def t188 : Tree (Fin 3) := .node 0 t179 t185
theorem cert188 : Certified t188 ({(1, false), (2, true)}) w188 := by
  apply certified_node cert179 cert185 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w179, w185, w188]

def w189 : Fin 8 → ℝ := ![(436073 / 524288), 0, (8863 / 524288), (12375 / 524288), (5795 / 262144), (12413 / 524288), (9093 / 524288), (33881 / 524288)]
def t189 : Tree (Fin 3) := .node 0 t181 t183
theorem cert189 : Certified t189 ({(1, false), (2, false)}) w189 := by
  apply certified_node cert181 cert183 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w181, w183, w189]

def w190 : Fin 8 → ℝ := ![(242517 / 262144), (1 / 524288), (533 / 65536), (7465 / 524288), (4829 / 524288), (1795 / 262144), (4025 / 524288), (1885 / 65536)]
def t190 : Tree (Fin 3) := .node 2 t0 t177
theorem cert190 : Certified t190 ({(0, true), (1, true)}) w190 := by
  apply certified_node cert0 cert177 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w177, w190]

def w191 : Fin 8 → ℝ := ![(453533 / 524288), 0, (229 / 16384), (1381 / 65536), (9093 / 524288), (8793 / 524288), (3663 / 262144), (27167 / 524288)]
def t191 : Tree (Fin 3) := .node 2 t179 t178
theorem cert191 : Certified t191 ({(0, true), (1, false)}) w191 := by
  apply certified_node cert179 cert178 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w179, w178, w191]

def w192 : Fin 8 → ℝ := ![(453533 / 524288), 0, (1737 / 131072), (8841 / 524288), (9473 / 524288), (5499 / 262144), (229 / 16384), (27167 / 524288)]
def t192 : Tree (Fin 3) := .node 1 t176 t185
theorem cert192 : Certified t192 ({(0, false), (2, true)}) w192 := by
  apply certified_node cert176 cert185 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w176, w185, w192]

def w193 : Fin 8 → ℝ := ![(436073 / 524288), 0, (9471 / 524288), (7973 / 262144), (5491 / 262144), (4421 / 262144), (9093 / 524288), (33881 / 524288)]
def t193 : Tree (Fin 3) := .node 1 t184 t178
theorem cert193 : Certified t193 ({(0, false), (2, false)}) w193 := by
  apply certified_node cert184 cert178 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w184, w178, w193]

def w194 : Fin 8 → ℝ := ![(453533 / 524288), 0, (1737 / 131072), (8841 / 524288), (9473 / 524288), (1375 / 65536), (3663 / 262144), (27167 / 524288)]
def t194 : Tree (Fin 3) := .node 2 t176 t183
theorem cert194 : Certified t194 ({(0, false), (1, true)}) w194 := by
  apply certified_node cert176 cert183 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w176, w183, w194]

def w195 : Fin 8 → ℝ := ![(436073 / 524288), 0, (9471 / 524288), (7973 / 262144), (5491 / 262144), (8841 / 524288), (4547 / 262144), (33881 / 524288)]
def t195 : Tree (Fin 3) := .node 2 t182 t178
theorem cert195 : Certified t195 ({(0, false), (1, false)}) w195 := by
  apply certified_node cert182 cert178 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w182, w178, w195]

def w196 : Fin 8 → ℝ := ![(921107 / 1048576), (1 / 1048576), (13735 / 1048576), (23411 / 1048576), (15811 / 1048576), (777 / 65536), (6559 / 524288), (48961 / 1048576)]
def t196 : Tree (Fin 3) := .node 0 t190 t193
theorem cert196 : Certified t196 ({(1, true), (2, false)}) w196 := by
  apply certified_node cert190 cert193 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w190, w193, w196]

def w197 : Fin 8 → ℝ := ![(444803 / 524288), 0, (16799 / 1048576), (13497 / 524288), (20075 / 1048576), (17635 / 1048576), (16419 / 1048576), (7631 / 131072)]
def t197 : Tree (Fin 3) := .node 0 t191 t193
theorem cert197 : Certified t197 ({(1, false), (2, false)}) w197 := by
  apply certified_node cert191 cert193 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w191, w193, w197]

def w198 : Fin 8 → ℝ := ![(977821 / 1048576), 0, (3475 / 524288), (8841 / 1048576), (9471 / 1048576), (5499 / 524288), (229 / 32768), (27167 / 1048576)]
def t198 : Tree (Fin 3) := .node 1 t0 t188
theorem cert198 : Certified t198 ({(0, true), (2, true)}) w198 := by
  apply certified_node cert0 cert188 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w188, w198]

def w199 : Fin 8 → ℝ := ![(977821 / 1048576), (1 / 524288), (1737 / 262144), (8841 / 1048576), (9471 / 1048576), (1377 / 131072), (3655 / 524288), (27167 / 1048576)]
def t199 : Tree (Fin 3) := .node 2 t0 t187
theorem cert199 : Certified t199 ({(0, true), (1, true)}) w199 := by
  apply certified_node cert0 cert187 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w187, w199]

def w200 : Fin 8 → ℝ := ![(921107 / 1048576), 0, (13735 / 1048576), (23411 / 1048576), (3953 / 262144), (6211 / 524288), (1641 / 131072), (48961 / 1048576)]
def t200 : Tree (Fin 3) := .node 1 t186 t195
theorem cert200 : Certified t200 ({(0, false), (2, true)}) w200 := by
  apply certified_node cert186 cert195 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w186, w195, w200]

def w201 : Fin 8 → ℝ := ![(444803 / 524288), 0, (15811 / 1048576), (663 / 32768), (21063 / 1048576), (23413 / 1048576), (16419 / 1048576), (7631 / 131072)]
def t201 : Tree (Fin 3) := .node 1 t194 t189
theorem cert201 : Certified t201 ({(0, false), (2, false)}) w201 := by
  apply certified_node cert194 cert189 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w194, w189, w201]

def w202 : Fin 8 → ℝ := ![(921107 / 1048576), 0, (13735 / 1048576), (23411 / 1048576), (3953 / 262144), (12423 / 1048576), (13127 / 1048576), (48961 / 1048576)]
def t202 : Tree (Fin 3) := .node 2 t186 t193
theorem cert202 : Certified t202 ({(0, false), (1, true)}) w202 := by
  apply certified_node cert186 cert193 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w186, w193, w202]

def w203 : Fin 8 → ℝ := ![(444803 / 524288), 0, (15811 / 1048576), (663 / 32768), (21063 / 1048576), (23411 / 1048576), (16421 / 1048576), (7631 / 131072)]
def t203 : Tree (Fin 3) := .node 2 t192 t189
theorem cert203 : Certified t203 ({(0, false), (1, false)}) w203 := by
  apply certified_node cert192 cert189 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w192, w189, w203]

def w204 : Fin 8 → ℝ := ![(1969683 / 2097152), 0, (13735 / 2097152), (23411 / 2097152), (3953 / 524288), (6211 / 1048576), (1641 / 262144), (48961 / 2097152)]
def t204 : Tree (Fin 3) := .node 0 t0 t200
theorem cert204 : Certified t204 ({(1, true), (2, true)}) w204 := by
  apply certified_node cert0 cert200 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w200, w204]

def w205 : Fin 8 → ℝ := ![(1867427 / 2097152), (1 / 1048576), (22759 / 2097152), (30057 / 2097152), (15267 / 1048576), (34429 / 2097152), (23729 / 2097152), (88215 / 2097152)]
def t205 : Tree (Fin 3) := .node 0 t199 t201
theorem cert205 : Certified t205 ({(1, true), (2, false)}) w205 := by
  apply certified_node cert199 cert201 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w199, w201, w205]

def w206 : Fin 8 → ℝ := ![(1867427 / 2097152), 0, (22761 / 2097152), (30057 / 2097152), (15267 / 1048576), (34409 / 2097152), (23749 / 2097152), (88215 / 2097152)]
def t206 : Tree (Fin 3) := .node 0 t198 t203
theorem cert206 : Certified t206 ({(1, false), (2, true)}) w206 := by
  apply certified_node cert198 cert203 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w198, w203, w206]

def w207 : Fin 8 → ℝ := ![(1969683 / 2097152), (1 / 2097152), (13735 / 2097152), (23411 / 2097152), (15811 / 2097152), (777 / 131072), (6559 / 1048576), (48961 / 2097152)]
def t207 : Tree (Fin 3) := .node 2 t0 t196
theorem cert207 : Certified t207 ({(0, true), (1, true)}) w207 := by
  apply certified_node cert0 cert196 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w196, w207]

def w208 : Fin 8 → ℝ := ![(1867427 / 2097152), 0, (23749 / 2097152), (35835 / 2097152), (14773 / 1048576), (28633 / 2097152), (23747 / 2097152), (88215 / 2097152)]
def t208 : Tree (Fin 3) := .node 2 t198 t197
theorem cert208 : Certified t208 ({(0, true), (1, false)}) w208 := by
  apply certified_node cert198 cert197 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w198, w197, w208]

def w209 : Fin 8 → ℝ := ![(1810713 / 2097152), 0, (15267 / 1048576), (50405 / 2097152), (35887 / 2097152), (15029 / 1048576), (14773 / 1048576), (110009 / 2097152)]
def t209 : Tree (Fin 3) := .node 1 t202 t197
theorem cert209 : Certified t209 ({(0, false), (2, false)}) w209 := by
  apply certified_node cert202 cert197 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w202, w197, w209]

def w210 : Fin 8 → ℝ := ![(1810713 / 2097152), 0, (15267 / 1048576), (50405 / 2097152), (35887 / 2097152), (30057 / 2097152), (29547 / 2097152), (110009 / 2097152)]
def t210 : Tree (Fin 3) := .node 2 t200 t197
theorem cert210 : Certified t210 ({(0, false), (1, false)}) w210 := by
  apply certified_node cert200 cert197 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w200, w197, w210]

def w211 : Fin 8 → ℝ := ![(945099 / 1048576), (1 / 4194304), (44269 / 4194304), (9227 / 524288), (25849 / 2097152), (21245 / 2097152), (5333 / 524288), (79485 / 2097152)]
def t211 : Tree (Fin 3) := .node 0 t207 t209
theorem cert211 : Certified t211 ({(1, true), (2, false)}) w211 := by
  apply certified_node cert207 cert209 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w207, w209, w211]

def w212 : Fin 8 → ℝ := ![(919535 / 1048576), 0, (54283 / 4194304), (2695 / 131072), (65433 / 4194304), (58691 / 4194304), (53293 / 4194304), (12389 / 262144)]
def t212 : Tree (Fin 3) := .node 0 t208 t209
theorem cert212 : Certified t212 ({(1, false), (2, false)}) w212 := by
  apply certified_node cert208 cert209 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w208, w209, w212]

def w213 : Fin 8 → ℝ := ![(3964579 / 4194304), 0, (22761 / 4194304), (30057 / 4194304), (15267 / 2097152), (34409 / 4194304), (23749 / 4194304), (88215 / 4194304)]
def t213 : Tree (Fin 3) := .node 1 t0 t206
theorem cert213 : Certified t213 ({(0, true), (2, true)}) w213 := by
  apply certified_node cert0 cert206 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w206, w213]

def w214 : Fin 8 → ℝ := ![(3964579 / 4194304), (1 / 2097152), (22759 / 4194304), (30057 / 4194304), (15267 / 2097152), (34429 / 4194304), (23729 / 4194304), (88215 / 4194304)]
def t214 : Tree (Fin 3) := .node 2 t0 t205
theorem cert214 : Certified t214 ({(0, true), (1, true)}) w214 := by
  apply certified_node cert0 cert205 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w205, w214]

def w215 : Fin 8 → ℝ := ![(945099 / 1048576), 0, (44269 / 4194304), (9227 / 524288), (51699 / 4194304), (42479 / 4194304), (42675 / 4194304), (79485 / 2097152)]
def t215 : Tree (Fin 3) := .node 1 t204 t210
theorem cert215 : Certified t215 ({(0, false), (2, true)}) w215 := by
  apply certified_node cert204 cert210 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w204, w210, w215]

def w216 : Fin 8 → ℝ := ![(945099 / 1048576), 0, (44269 / 4194304), (9227 / 524288), (51699 / 4194304), (2655 / 262144), (21337 / 2097152), (79485 / 2097152)]
def t216 : Tree (Fin 3) := .node 2 t204 t209
theorem cert216 : Certified t216 ({(0, false), (1, true)}) w216 := by
  apply certified_node cert204 cert209 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w204, w209, w216]

def w217 : Fin 8 → ℝ := ![(7744975 / 8388608), (1 / 4194304), (16757 / 2097152), (103873 / 8388608), (82233 / 8388608), (76909 / 8388608), (66403 / 8388608), (247185 / 8388608)]
def t217 : Tree (Fin 3) := .node 0 t214 t216
theorem cert217 : Certified t217 ({(1, true)}) w217 := by
  apply certified_node cert214 cert216 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w214, w216, w217]

def w218 : Fin 8 → ℝ := ![(1993675 / 2097152), (1 / 8388608), (44269 / 8388608), (9227 / 1048576), (25849 / 4194304), (21245 / 4194304), (5333 / 1048576), (79485 / 4194304)]
def t218 : Tree (Fin 3) := .node 2 t0 t211
theorem cert218 : Certified t218 ({(0, true), (1, true)}) w218 := by
  apply certified_node cert0 cert211 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w0, w211, w218]

def w219 : Fin 8 → ℝ := ![(7642719 / 8388608), 0, (19261 / 2097152), (116297 / 8388608), (95967 / 8388608), (23275 / 2097152), (38521 / 4194304), (286439 / 8388608)]
def t219 : Tree (Fin 3) := .node 2 t213 t212
theorem cert219 : Certified t219 ({(0, true), (1, false)}) w219 := by
  apply certified_node cert213 cert212 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w213, w212, w219]

def w220 : Fin 8 → ℝ := ![(932317 / 1048576), 0, (12319 / 1048576), (20007 / 1048576), (29283 / 2097152), (50585 / 4194304), (2999 / 262144), (178597 / 4194304)]
def t220 : Tree (Fin 3) := .node 2 t215 t212
theorem cert220 : Certified t220 ({(0, false), (1, false)}) w220 := by
  apply certified_node cert215 cert212 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w215, w212, w220]

def w221 : Fin 8 → ℝ := ![(15617419 / 16777216), (1 / 16777216), (121313 / 16777216), (190113 / 16777216), (147665 / 16777216), (67795 / 8388608), (59853 / 8388608), (445409 / 16777216)]
def t221 : Tree (Fin 3) := .node 1 t218 t219
theorem cert221 : Certified t221 ({(0, true)}) w221 := by
  apply certified_node cert218 cert219 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w218, w219, w221]

def w222 : Fin 8 → ℝ := ![(15203511 / 16777216), (1 / 8388608), (41395 / 4194304), (263929 / 16777216), (199365 / 16777216), (178079 / 16777216), (162371 / 16777216), (604379 / 16777216)]
def t222 : Tree (Fin 3) := .node 1 t217 t220
theorem cert222 : Certified t222 ({(0, false)}) w222 := by
  apply certified_node cert217 cert220 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w217, w220, w222]

def w223 : Fin 8 → ℝ := ![(15410465 / 16777216), (3 / 33554432), (286893 / 33554432), (227021 / 16777216), (173515 / 16777216), (313669 / 33554432), (282077 / 33554432), (262447 / 8388608)]
def t223 : Tree (Fin 3) := .node 0 t221 t222
theorem cert223 : Certified t223 (∅) w223 := by
  apply certified_node cert221 cert222 (by decide) (by decide) (by decide)
  intro j
  fin_cases j <;> norm_num [w221, w222, w223]

end
end Kunisky.FiniteCounterexample

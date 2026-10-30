import NAGBasic

noncomputable section
set_option autoImplicit false
namespace DiscreteNesterov
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Linear conjugacy of the literal algorithm, including its prescribed first step. -/
theorem nag_map (l : E →L[ℝ] D) (r h s : ℝ) (G : E → E) (J : D → D)
    (b : E) (hj : ∀ x, h^2 • l (G x)=s^2 • J (l x)) (k : ℕ) :
    l (nagX r h G b k)=nagX r s J (l b) k ∧
    l (nagY r h G b k)=nagY r s J (l b) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hx : l (nagX r h G b (k+1))=nagX r s J (l b) (k+1) := by
      simp only [nagX_succ, map_sub, map_smul, hj, ih.2]
    refine ⟨hx, ?_⟩
    simp only [nagY_succ, map_add, map_sub, map_smul, hx, ih.1]

end DiscreteNesterov

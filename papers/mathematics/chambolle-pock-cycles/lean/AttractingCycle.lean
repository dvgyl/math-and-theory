import FiniteCycle

/-!
# Finite capture by strict polytopal Chambolle--Pock cycles

Strict inequalities at all other vertices imply that the metric projection is
locally constant.  Applying this fact twice proves that every sufficiently small
perturbation of a certified cycle state is captured by the exact cycle in one
iteration.  All maps are the actual unique global projection minimizers from
`FiniteCycle`.
-/

set_option autoImplicit false

noncomputable section

namespace FiniteCP

variable {n d : ℕ} [NeZero n]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- Strict vertex-normal inequalities give an open neighborhood of centers with
exactly the same unique metric projection. -/
theorem project_locally_constant (x : Fin n → Space d) (c : Space d) (i : Fin n)
    (h : ∀ j, j ≠ i → ⟪c - x i, x j - x i⟫ < 0) :
    ∀ᶠ u in nhds c, project x u = x i := by
  have he : ∀ᶠ u in nhds c, ∀ j, ⟪u - x i, x j - x i⟫ ≤ 0 := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hji : j = i
    · subst j
      exact Filter.Eventually.of_forall (by intro u; simp)
    · have hc : Continuous (fun u : Space d => ⟪u - x i, x j - x i⟫) := by fun_prop
      have hlt : ∀ᶠ u in nhds c, ⟪u - x i, x j - x i⟫ < 0 :=
        (isOpen_lt hc continuous_const).mem_nhds (h j hji)
      filter_upwards [hlt] with u hu
      exact hu.le
  filter_upwards [he] with u hu
  exact project_vertex x u i hu

theorem normalCertificate_of_strict_normals (x y : Fin n → Space d) (κ θ : ℝ)
    (hp : ∀ i j, j ≠ nextIndex i →
      ⟪x i - y i - x (nextIndex i), x j - x (nextIndex i)⟫ < 0)
    (hd : ∀ i j, j ≠ nextIndex i →
      ⟪y i + κ • ((1 + θ) • x (nextIndex i) - θ • x i) - y (nextIndex i),
        y j - y (nextIndex i)⟫ < 0) : NormalCertificate x y κ θ := by
  constructor
  · intro i j
    by_cases hji : j = nextIndex i
    · subst j
      simp
    · exact (hp i j hji).le
  · intro i j
    by_cases hji : j = nextIndex i
    · subst j
      simp
    · exact (hd i j hji).le

/-- An actual CP update is constant near a state whose next primal and dual
projection centers both satisfy strict vertex inequalities. -/
theorem cpMap_locally_constant (x y : Fin n → Space d) (κ θ : ℝ) (i : Fin n)
    (hp : ∀ j, j ≠ nextIndex i →
      ⟪x i - y i - x (nextIndex i), x j - x (nextIndex i)⟫ < 0)
    (hd : ∀ j, j ≠ nextIndex i →
      ⟪y i + κ • ((1 + θ) • x (nextIndex i) - θ • x i) - y (nextIndex i),
        y j - y (nextIndex i)⟫ < 0) :
    ∀ᶠ w in nhds (x i, y i), cpMap x y κ θ w = (x (nextIndex i), y (nextIndex i)) := by
  have hpcenter := project_locally_constant x (x i - y i) (nextIndex i) hp
  have hdcenter := project_locally_constant y
    (y i + κ • ((1 + θ) • x (nextIndex i) - θ • x i)) (nextIndex i) hd
  have ht₁ : Filter.Tendsto (fun w : Space d × Space d => w.1 - w.2)
      (nhds (x i, y i)) (nhds (x i - y i)) := by
    change ContinuousAt (fun w : Space d × Space d => w.1 - w.2) (x i, y i)
    fun_prop
  have ht₂ : Filter.Tendsto
      (fun w : Space d × Space d => w.2 + κ • ((1 + θ) • x (nextIndex i) - θ • w.1))
      (nhds (x i, y i))
      (nhds (y i + κ • ((1 + θ) • x (nextIndex i) - θ • x i))) := by
    change ContinuousAt
      (fun w : Space d × Space d => w.2 + κ • ((1 + θ) • x (nextIndex i) - θ • w.1))
      (x i, y i)
    fun_prop
  have hx := ht₁.eventually hpcenter
  have hy := ht₂.eventually hdcenter
  filter_upwards [hx, hy] with w hwx hwy
  simp only [cpMap, hwx]
  exact Prod.ext rfl hwy

/-- Every sufficiently close initial state agrees exactly with the cycle from
its very first update onwards.  This is finite capture, stronger than merely
asymptotic attraction. -/
theorem cycle_one_step_capture (x y : Fin n → Space d) (κ θ : ℝ)
    (hp : ∀ i j, j ≠ nextIndex i →
      ⟪x i - y i - x (nextIndex i), x j - x (nextIndex i)⟫ < 0)
    (hd : ∀ i j, j ≠ nextIndex i →
      ⟪y i + κ • ((1 + θ) • x (nextIndex i) - θ • x i) - y (nextIndex i),
        y j - y (nextIndex i)⟫ < 0) (i : Fin n) :
    ∀ᶠ w in nhds (x i, y i), ∀ k : ℕ,
      (cpMap x y κ θ)^[k + 1] w = (cpMap x y κ θ)^[k + 1] (x i, y i) := by
  have hl := cpMap_locally_constant x y κ θ i (hp i) (hd i)
  have hc := normalCertificate_of_strict_normals x y κ θ hp hd
  have hs := certified_step x y κ θ hc i
  filter_upwards [hl] with w hw
  intro k
  simp only [Function.iterate_succ_apply, hw, hs]

theorem iterate_cycle_state_eq_orbit (x y : Fin n → Space d) (κ θ : ℝ)
    (h : NormalCertificate x y κ θ) (i : Fin n) (k : ℕ) :
    (cpMap x y κ θ)^[k] (x i, y i) = orbit x y (k + i.val) := by
  induction k with
  | zero => simpa using (orbit_subseq x y i 0).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have he : (k + 1) + i.val = (k + i.val) + 1 := by omega
    rw [he, orbit_recursion x y κ θ h]

/-- An open neighborhood of every strict cycle state consists entirely of
nonconvergent initial conditions. The proof uses exact capture of the cycle,
not a numerical or asymptotic stability test. -/
theorem nearby_iterates_not_convergent (x y : Fin n → Space d) (κ θ : ℝ)
    (hp : ∀ i j, j ≠ nextIndex i →
      ⟪x i - y i - x (nextIndex i), x j - x (nextIndex i)⟫ < 0)
    (hd : ∀ i j, j ≠ nextIndex i →
      ⟪y i + κ • ((1 + θ) • x (nextIndex i) - θ • x i) - y (nextIndex i),
        y j - y (nextIndex i)⟫ < 0)
    (a b : Fin n) (hne : x a ≠ x b) (i : Fin n) :
    ∀ᶠ w in nhds (x i, y i),
      ¬ ∃ v, Filter.Tendsto (fun k : ℕ => (cpMap x y κ θ)^[k] w)
        Filter.atTop (nhds v) := by
  have hc := normalCertificate_of_strict_normals x y κ θ hp hd
  have hcapture := cycle_one_step_capture x y κ θ hp hd i
  filter_upwards [hcapture] with w hw
  rintro ⟨v, hv⟩
  have hstate : Filter.Tendsto (fun k : ℕ => (cpMap x y κ θ)^[k] (x i, y i))
      Filter.atTop (nhds v) := by
    apply (Filter.tendsto_add_atTop_iff_nat 1).mp
    simpa only [Function.comp_def, hw] using hv.comp (Filter.tendsto_add_atTop_nat 1)
  have hshift : Filter.Tendsto (fun k : ℕ => orbit x y (k + i.val))
      Filter.atTop (nhds v) := by
    simpa only [iterate_cycle_state_eq_orbit x y κ θ hc i] using hstate
  have ho : Filter.Tendsto (orbit x y) Filter.atTop (nhds v) :=
    (Filter.tendsto_add_atTop_iff_nat i.val).mp hshift
  exact orbit_not_convergent x y a b hne ⟨v, ho⟩

end FiniteCP

#print axioms FiniteCP.cpMap_locally_constant
#print axioms FiniteCP.cycle_one_step_capture
#print axioms FiniteCP.nearby_iterates_not_convergent

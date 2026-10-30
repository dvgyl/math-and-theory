module

public import MatCP1Converse.ForwardDilation
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

namespace MatCP1Converse

variable {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

def dilationEval (A0 A1 : V →ₗ[F] W) (c d t : F) :
    (V × (V × W)) →ₗ[F] (W × (W × V)) :=
  dilationConstant A0 c d + t • dilationLinear A1

@[simp] theorem dilationEval_apply (A0 A1 : V →ₗ[F] W) (c d t : F)
    (u v : V) (w : W) :
    dilationEval A0 A1 c d t (u, v, w) =
      ((A0 + t • A1) u + w, -(t - c) • w, u - (t - d) • v) :=
  dilation_evaluation A0 A1 c d t u v w

/-- Full-column factor of the coefficient evaluated at `d`. -/
def dilationELeft (A0 A1 : V →ₗ[F] W) (c d : F) :
    (V × W) →ₗ[F] (W × (W × V)) :=
  let u := LinearMap.fst F V W
  let w := LinearMap.snd F V W
  ((A0 + d • A1).comp u + w).prod (((c - d) • w).prod u)

def dilationERight : (V × (V × W)) →ₗ[F] (V × W) :=
  (LinearMap.fst F V (V × W)).prod
    ((LinearMap.snd F V W).comp (LinearMap.snd F V (V × W)))

/-- The same internal space `V × W` is used for the other coefficient. -/
def dilationHLeft : (V × W) →ₗ[F] (W × (W × V)) :=
  (LinearMap.snd F V W).prod ((0 : (V × W) →ₗ[F] W).prod (LinearMap.fst F V W))

def dilationHRight (A0 A1 : V →ₗ[F] W) (c d : F) :
    (V × (V × W)) →ₗ[F] (V × W) :=
  let u := LinearMap.fst F V (V × W)
  let v := (LinearMap.fst F V W).comp (LinearMap.snd F V (V × W))
  let w := (LinearMap.snd F V W).comp (LinearMap.snd F V (V × W))
  (u + (d - c) • v).prod ((A0 + c • A1).comp u + w)

def dilationKernelLift (A0 A1 : V →ₗ[F] W) (d : F) :
    V →ₗ[F] ((V × W) × (V × W)) :=
  (LinearMap.id.prod (0 : V →ₗ[F] W)).prod
    ((-(LinearMap.id : V →ₗ[F] V)).prod (-(A0 + d • A1)))

def dilationQuotient (A0 A1 : V →ₗ[F] W) (c : F) :
    ((V × W) × (V × W)) →ₗ[F] W :=
  let e := LinearMap.fst F (V × W) (V × W)
  let h := LinearMap.snd F (V × W) (V × W)
  (A0 + c • A1).comp ((LinearMap.fst F V W).comp e) +
    (LinearMap.snd F V W).comp e - (LinearMap.snd F V W).comp h

@[simp] theorem dilationELeft_apply (A0 A1 : V →ₗ[F] W) (c d : F)
    (u : V) (w : W) :
    dilationELeft A0 A1 c d (u, w) = ((A0 + d • A1) u + w, (c - d) • w, u) := rfl

@[simp] theorem dilationERight_apply (u v : V) (w : W) :
    dilationERight (F := F) (u, v, w) = (u, w) := rfl

@[simp] theorem dilationHLeft_apply (u : V) (w : W) :
    dilationHLeft (F := F) (u, w) = (w, 0, u) := rfl

@[simp] theorem dilationHRight_apply (A0 A1 : V →ₗ[F] W) (c d : F)
    (u v : V) (w : W) :
    dilationHRight A0 A1 c d (u, v, w) =
      (u + (d - c) • v, (A0 + c • A1) u + w) := rfl

@[simp] theorem dilationKernelLift_apply (A0 A1 : V →ₗ[F] W) (d : F) (x : V) :
    dilationKernelLift A0 A1 d x = ((x, 0), (-x, -(A0 + d • A1) x)) := rfl

@[simp] theorem dilationQuotient_apply (A0 A1 : V →ₗ[F] W) (c : F)
    (u k : V) (w h : W) :
    dilationQuotient A0 A1 c ((u, w), (k, h)) = (A0 + c • A1) u + w - h := rfl

theorem dilation_factor_E (A0 A1 : V →ₗ[F] W) (c d : F) :
    (dilationELeft A0 A1 c d).comp dilationERight = dilationEval A0 A1 c d d := by
  apply LinearMap.ext
  rintro ⟨u, v, w⟩
  simp [neg_sub]

theorem dilation_factor_H (A0 A1 : V →ₗ[F] W) (c d : F) :
    dilationHLeft.comp (dilationHRight A0 A1 c d) = dilationEval A0 A1 c d c := by
  apply LinearMap.ext
  rintro ⟨u, v, w⟩
  simp only [LinearMap.comp_apply, dilationHRight_apply, dilationHLeft_apply,
    dilationEval_apply, sub_self, neg_zero, zero_smul]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · module

theorem dilationELeft_injective (A0 A1 : V →ₗ[F] W) (c d : F) :
    Function.Injective (dilationELeft A0 A1 c d) := by
  rintro ⟨u, w⟩ ⟨u', w'⟩ h
  have hu := congrArg (fun y => y.2.2) h
  have hw := congrArg Prod.fst h
  change u = u' at hu
  change (A0 + d • A1) u + w = (A0 + d • A1) u' + w' at hw
  rw [hu] at hw
  exact Prod.ext hu (add_left_cancel hw)

theorem dilationERight_surjective : Function.Surjective (dilationERight (F := F) (V := V) (W := W)) := by
  rintro ⟨u, w⟩
  exact ⟨(u, 0, w), rfl⟩

theorem dilationHLeft_injective : Function.Injective (dilationHLeft (F := F) (V := V) (W := W)) := by
  rintro ⟨u, w⟩ ⟨u', w'⟩ h
  exact Prod.ext (congrArg (fun y => y.2.2) h) (congrArg Prod.fst h)

theorem dilationHRight_surjective (A0 A1 : V →ₗ[F] W) (c d : F) :
    Function.Surjective (dilationHRight A0 A1 c d) := by
  rintro ⟨u, w⟩
  refine ⟨(u, 0, w - (A0 + c • A1) u), ?_⟩
  simp

theorem dilationKernelLift_injective (A0 A1 : V →ₗ[F] W) (d : F) :
    Function.Injective (dilationKernelLift A0 A1 d) := by
  intro x y h
  exact congrArg (fun v => v.1.1) h

theorem dilationQuotient_surjective (A0 A1 : V →ₗ[F] W) (c : F) :
    Function.Surjective (dilationQuotient A0 A1 c) := by
  intro w
  refine ⟨((0, 0), (0, -w)), ?_⟩
  simp

/-- The common right factor is injective at distinct anchors. -/
theorem dilation_factors_prod_injective (A0 A1 : V →ₗ[F] W) (c d : F) (hcd : c ≠ d) :
    Function.Injective (dilationERight.prod (dilationHRight A0 A1 c d)) := by
  rintro ⟨u, v, w⟩ ⟨u', v', w'⟩ h
  have hu := congrArg (fun x => x.1.1) h
  have hw := congrArg (fun x => x.1.2) h
  have hv := congrArg (fun x => x.2.1) h
  change u = u' at hu
  change w = w' at hw
  change u + (d - c) • v = u' + (d - c) • v' at hv
  rw [hu] at hv
  have hvs := congrArg (fun x : V => (d - c)⁻¹ • x) (add_left_cancel hv)
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr hcd.symm
  simp only [smul_smul, inv_mul_cancel₀ hdc, one_smul] at hvs
  exact Prod.ext hu (Prod.ext hvs hw)

/-- The common left factor is surjective at distinct anchors. -/
theorem dilation_factors_coprod_surjective (A0 A1 : V →ₗ[F] W) (c d : F) (hcd : c ≠ d) :
    Function.Surjective ((dilationELeft A0 A1 c d).coprod dilationHLeft) := by
  rintro ⟨f, g, h⟩
  let w : W := (c - d)⁻¹ • g
  refine ⟨((0, w), (h, f - w)), ?_⟩
  have hδ : c - d ≠ 0 := sub_ne_zero.mpr hcd
  simp only [LinearMap.coprod_apply, dilationELeft_apply, dilationHLeft_apply, map_zero,
    zero_add, Prod.mk_add_mk, add_zero]
  apply Prod.ext
  · module
  · apply Prod.ext
    · simp [w, smul_smul, hδ]
    · rfl

theorem dilation_complement_constant (A0 A1 : V →ₗ[F] W) (c d : F) :
    (dilationQuotient A0 A1 c).comp
      (((0 : (V × W) →ₗ[F] (V × W)).prodMap LinearMap.id).comp
        (dilationKernelLift A0 A1 d)) = A0 + d • A1 := by
  apply LinearMap.ext
  intro x
  simp [dilationQuotient]

theorem dilation_complement_linear (A0 A1 : V →ₗ[F] W) (c d : F) :
    (dilationQuotient A0 A1 c).comp
      ((LinearMap.id.prodMap (0 : (V × W) →ₗ[F] (V × W))).comp
        (dilationKernelLift A0 A1 d)) = A0 + c • A1 := by
  apply LinearMap.ext
  intro x
  simp [dilationQuotient]

/-- The displayed quotient has exactly the range of the joint right factor
as its kernel. This is proved from the actual coordinate equations. -/
theorem dilationQuotient_ker (A0 A1 : V →ₗ[F] W) (c d : F) (hcd : c ≠ d) :
    LinearMap.ker (dilationQuotient A0 A1 c) =
      LinearMap.range (dilationERight.prod (dilationHRight A0 A1 c d)) := by
  apply Submodule.ext
  rintro ⟨⟨u, w⟩, k, h⟩
  constructor
  · intro hx
    change (A0 + c • A1) u + w - h = 0 at hx
    have hdc : d - c ≠ 0 := sub_ne_zero.mpr hcd.symm
    refine ⟨(u, (d - c)⁻¹ • (k - u), w), ?_⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · change u + (d - c) • ((d - c)⁻¹ • (k - u)) = k
        simp only [smul_smul, mul_inv_cancel₀ hdc, one_smul]
        module
      · exact sub_eq_zero.mp hx
  · rintro ⟨x, hx⟩
    rw [← hx]
    change dilationQuotient A0 A1 c
      ((dilationERight.prod (dilationHRight A0 A1 c d)) x) = 0
    rcases x with ⟨u', v', w'⟩
    simp

/-- The displayed kernel map parametrizes the whole kernel of the joint left
factor, including all zero-dimensional edge cases. -/
theorem dilationKernelLift_range (A0 A1 : V →ₗ[F] W) (c d : F) (hcd : c ≠ d) :
    LinearMap.range (dilationKernelLift A0 A1 d) =
      LinearMap.ker ((dilationELeft A0 A1 c d).coprod dilationHLeft) := by
  apply Submodule.ext
  rintro ⟨⟨u, w⟩, k, h⟩
  constructor
  · rintro ⟨x, hx⟩
    rw [← hx]
    change ((dilationELeft A0 A1 c d).coprod dilationHLeft)
      (dilationKernelLift A0 A1 d x) = 0
    simp
  · intro hx
    change ((dilationELeft A0 A1 c d).coprod dilationHLeft) ((u, w), (k, h)) = 0 at hx
    have hu := congrArg (fun y => y.2.2) hx
    have hw := congrArg (fun y => y.2.1) hx
    have hh := congrArg Prod.fst hx
    simp only [LinearMap.coprod_apply, dilationELeft_apply, dilationHLeft_apply,
      Prod.mk_add_mk, add_zero] at hu hw hh
    change u + k = 0 at hu
    change (c - d) • w = 0 at hw
    change (A0 + d • A1) u + w + h = 0 at hh
    have hδ : c - d ≠ 0 := sub_ne_zero.mpr hcd
    have hw' : w = 0 := by
      have hh := congrArg (fun y : W => (c - d)⁻¹ • y) hw
      simpa only [smul_smul, inv_mul_cancel₀ hδ, one_smul, smul_zero] using hh
    have hk : k = -u := by
      calc
        k = (u + k) - u := by abel
        _ = -u := by rw [hu]; simp
    have hh' : h = -(A0 + d • A1) u := by
      rw [hw', add_zero] at hh
      calc
        h = ((A0 + d • A1) u + h) - (A0 + d • A1) u := by abel
        _ = -(A0 + d • A1) u := by rw [hh]; simp
    exact ⟨u, by simp [hw', hk, hh']⟩

theorem dilation_anchor_pair_injective (A0 A1 : V →ₗ[F] W) (c d : F) (hcd : c ≠ d) :
    Function.Injective ((dilationEval A0 A1 c d d).prod (dilationEval A0 A1 c d c)) := by
  intro x y h
  apply dilation_factors_prod_injective A0 A1 c d hcd
  apply Prod.ext
  · apply dilationELeft_injective A0 A1 c d
    have h' := congrArg Prod.fst h
    change dilationEval A0 A1 c d d x = dilationEval A0 A1 c d d y at h'
    rw [← dilation_factor_E] at h'
    exact h'
  · apply dilationHLeft_injective (F := F) (V := V) (W := W)
    have h' := congrArg Prod.snd h
    change dilationEval A0 A1 c d c x = dilationEval A0 A1 c d c y at h'
    rw [← dilation_factor_H] at h'
    exact h'

theorem dilation_anchor_coprod_surjective (A0 A1 : V →ₗ[F] W) (c d : F) (hcd : c ≠ d) :
    Function.Surjective ((dilationEval A0 A1 c d d).coprod (dilationEval A0 A1 c d c)) := by
  intro z
  obtain ⟨⟨e, h⟩, heh⟩ := dilation_factors_coprod_surjective A0 A1 c d hcd z
  obtain ⟨x, hx⟩ := dilationERight_surjective (F := F) e
  obtain ⟨y, hy⟩ := dilationHRight_surjective A0 A1 c d h
  refine ⟨(x, y), ?_⟩
  rw [← dilation_factor_E, ← dilation_factor_H]
  change dilationELeft A0 A1 c d (dilationERight x) +
    dilationHLeft (dilationHRight A0 A1 c d y) = z
  rw [hx, hy]
  exact heh

theorem dilation_anchor_ker_inf (A0 A1 : V →ₗ[F] W) (c d : F) (hcd : c ≠ d) :
    LinearMap.ker (dilationEval A0 A1 c d d) ⊓
      LinearMap.ker (dilationEval A0 A1 c d c) = ⊥ := by
  simpa only [LinearMap.ker_prod] using
    LinearMap.ker_eq_bot.mpr (dilation_anchor_pair_injective A0 A1 c d hcd)

theorem dilation_anchor_range_sup (A0 A1 : V →ₗ[F] W) (c d : F) (hcd : c ≠ d) :
    LinearMap.range (dilationEval A0 A1 c d d) ⊔
      LinearMap.range (dilationEval A0 A1 c d c) = ⊤ := by
  simpa only [LinearMap.range_coprod] using
    LinearMap.range_eq_top.mpr (dilation_anchor_coprod_surjective A0 A1 c d hcd)

section FiniteRank

variable [FiniteDimensional F V] [FiniteDimensional F W]

theorem dilation_rank_at_d (A0 A1 : V →ₗ[F] W) (c d : F) :
    Module.finrank F (LinearMap.range (dilationEval A0 A1 c d d)) =
      Module.finrank F V + Module.finrank F W := by
  have hr : LinearMap.range (dilationEval A0 A1 c d d) =
      LinearMap.range (dilationELeft A0 A1 c d) := by
    rw [← dilation_factor_E]
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨dilationERight x, rfl⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := dilationERight_surjective (F := F) x
      exact ⟨y, by change dilationELeft A0 A1 c d (dilationERight y) = _; rw [hy]⟩
  rw [hr, LinearMap.finrank_range_of_inj (dilationELeft_injective A0 A1 c d),
    Module.finrank_prod]

theorem dilation_rank_at_c (A0 A1 : V →ₗ[F] W) (c d : F) :
    Module.finrank F (LinearMap.range (dilationEval A0 A1 c d c)) =
      Module.finrank F V + Module.finrank F W := by
  have hr : LinearMap.range (dilationEval A0 A1 c d c) =
      LinearMap.range (dilationHLeft (F := F) (V := V) (W := W)) := by
    rw [← dilation_factor_H]
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨dilationHRight A0 A1 c d x, rfl⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := dilationHRight_surjective A0 A1 c d x
      exact ⟨y, by change dilationHLeft (dilationHRight A0 A1 c d y) = _; rw [hy]⟩
  rw [hr, LinearMap.finrank_range_of_inj dilationHLeft_injective, Module.finrank_prod]

end FiniteRank

end MatCP1Converse

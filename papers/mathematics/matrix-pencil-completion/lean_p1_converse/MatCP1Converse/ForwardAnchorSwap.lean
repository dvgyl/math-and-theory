module

public import MatCP1Converse.ForwardDilation

@[expose] public section

namespace MatCP1Converse

variable {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- The constant source shear interchanging the two dilation anchors. -/
def dilationSwapSource (A0 A1 : V →ₗ[F] W) (c d : F) :
    (V × (V × W)) →ₗ[F] (V × (V × W)) :=
  let u := LinearMap.fst F V (V × W)
  let v := (LinearMap.fst F V W).comp (LinearMap.snd F V (V × W))
  let w := (LinearMap.snd F V W).comp (LinearMap.snd F V (V × W))
  (u + (c - d) • v).prod
    (v.prod (w - (c - d) • A1.comp u - (c - d) • (A0 + c • A1).comp v))

/-- The constant target shear interchanging the two dilation anchors. -/
def dilationSwapTarget (A0 A1 : V →ₗ[F] W) (c d : F) :
    (W × (W × V)) →ₗ[F] (W × (W × V)) :=
  let f := LinearMap.fst F W (W × V)
  let g := (LinearMap.fst F W V).comp (LinearMap.snd F W (W × V))
  let h := (LinearMap.snd F W V).comp (LinearMap.snd F W (W × V))
  (f + (c - d) • A1.comp h).prod
    ((g - (c - d) • f + (c - d) • (A0 + d • A1).comp h).prod h)

@[simp] theorem dilationSwapSource_apply (A0 A1 : V →ₗ[F] W) (c d : F)
    (u v : V) (w : W) :
    dilationSwapSource A0 A1 c d (u, v, w) =
      (u + (c - d) • v, v,
        w - (c - d) • A1 u - (c - d) • (A0 + c • A1) v) := rfl

@[simp] theorem dilationSwapTarget_apply (A0 A1 : V →ₗ[F] W) (c d : F)
    (f g : W) (h : V) :
    dilationSwapTarget A0 A1 c d (f, g, h) =
      (f + (c - d) • A1 h,
        g - (c - d) • f + (c - d) • (A0 + d • A1) h, h) := rfl

theorem dilationSwapSource_comp_reverse (A0 A1 : V →ₗ[F] W) (c d : F) :
    (dilationSwapSource A0 A1 c d).comp (dilationSwapSource A0 A1 d c) =
      LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨u, v, w⟩
  simp only [LinearMap.comp_apply, dilationSwapSource_apply, LinearMap.id_apply,
    LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul]
  apply Prod.ext
  · module
  · apply Prod.ext
    · rfl
    · module

theorem dilationSwapTarget_comp_reverse (A0 A1 : V →ₗ[F] W) (c d : F) :
    (dilationSwapTarget A0 A1 c d).comp (dilationSwapTarget A0 A1 d c) =
      LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨f, g, h⟩
  simp only [LinearMap.comp_apply, dilationSwapTarget_apply, LinearMap.id_apply,
    LinearMap.add_apply, LinearMap.smul_apply]
  apply Prod.ext
  · module
  · apply Prod.ext
    · module
    · rfl

def dilationSwapSourceEquiv (A0 A1 : V →ₗ[F] W) (c d : F) :
    (V × (V × W)) ≃ₗ[F] (V × (V × W)) :=
  LinearEquiv.ofLinearMap (dilationSwapSource A0 A1 c d) (dilationSwapSource A0 A1 d c)
    (dilationSwapSource_comp_reverse A0 A1 c d) (dilationSwapSource_comp_reverse A0 A1 d c)

def dilationSwapTargetEquiv (A0 A1 : V →ₗ[F] W) (c d : F) :
    (W × (W × V)) ≃ₗ[F] (W × (W × V)) :=
  LinearEquiv.ofLinearMap (dilationSwapTarget A0 A1 c d) (dilationSwapTarget A0 A1 d c)
    (dilationSwapTarget_comp_reverse A0 A1 c d) (dilationSwapTarget_comp_reverse A0 A1 d c)

/-- Universal constant strict equivalence between the two anchor orientations.
This holds even at eigenvalues of the input pencil, and even when `c = d`. -/
theorem dilation_anchor_swap_coefficients (A0 A1 : V →ₗ[F] W) (c d : F) (i : Bool) :
    (dilationSwapTargetEquiv A0 A1 c d).toLinearMap.comp
      ((dilationFamily A0 A1 c d i).comp
        (dilationSwapSourceEquiv A0 A1 c d).toLinearMap) =
      dilationFamily A0 A1 d c i := by
  apply LinearMap.ext
  rintro ⟨u, v, w⟩
  change dilationSwapTarget A0 A1 c d
    (dilationFamily A0 A1 c d i (dilationSwapSource A0 A1 c d (u, v, w))) =
      dilationFamily A0 A1 d c i (u, v, w)
  cases i <;>
    simp only [dilationFamily, Bool.false_eq_true, ite_false, ite_true,
      dilationSwapSource_apply, dilationConstant_apply, dilationLinear_apply,
      dilationSwapTarget_apply, LinearMap.add_apply, LinearMap.smul_apply,
      map_add, map_smul, map_neg]
  all_goals
    apply Prod.ext
    · module
    · apply Prod.ext <;> module

theorem jointCompression_dilation_anchor_swap (A0 A1 : V →ₗ[F] W) (c d : F) :
    MatCP1.JointCompression (dilationFamily A0 A1 d c) (dilationFamily A0 A1 c d) := by
  exact ⟨(dilationSwapTargetEquiv A0 A1 c d).toLinearMap,
    (dilationSwapSourceEquiv A0 A1 c d).toLinearMap,
    (dilationSwapTargetEquiv A0 A1 c d).surjective,
    (dilationSwapSourceEquiv A0 A1 c d).injective,
    dilation_anchor_swap_coefficients A0 A1 c d⟩

end MatCP1Converse

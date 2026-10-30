module

public import MatCP1.Compression
public import Mathlib.Tactic.Module

@[expose] public section

namespace MatCP1Converse

variable {F V W E G : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [AddCommGroup E] [Module F E] [AddCommGroup G] [Module F G]

/-- The constant coefficient of the three-block dilation. -/
def dilationConstant (A : V →ₗ[F] W) (c d : F) :
    (V × (V × W)) →ₗ[F] (W × (W × V)) :=
  let u := LinearMap.fst F V (V × W)
  let v := (LinearMap.fst F V W).comp (LinearMap.snd F V (V × W))
  let w := (LinearMap.snd F V W).comp (LinearMap.snd F V (V × W))
  (A.comp u + w).prod ((c • w).prod (u + d • v))

/-- The linear coefficient of the three-block dilation. -/
def dilationLinear (A : V →ₗ[F] W) :
    (V × (V × W)) →ₗ[F] (W × (W × V)) :=
  let u := LinearMap.fst F V (V × W)
  let v := (LinearMap.fst F V W).comp (LinearMap.snd F V (V × W))
  let w := (LinearMap.snd F V W).comp (LinearMap.snd F V (V × W))
  (A.comp u).prod ((-w).prod (-v))

/-- Both actual coefficients of the dilation, indexed by `Bool`. -/
def dilationFamily (A0 A1 : V →ₗ[F] W) (c d : F) :
    Bool → (V × (V × W)) →ₗ[F] (W × (W × V)) :=
  fun i => if i then dilationLinear A1 else dilationConstant A0 c d

/-- Both coefficients of `(t-a) I`, including its constant term. -/
def scalarDilationFamily (a : F) : Bool → E →ₗ[F] E :=
  fun i => if i then LinearMap.id else -a • LinearMap.id

@[simp] theorem dilationConstant_apply (A : V →ₗ[F] W) (c d : F)
    (u v : V) (w : W) :
    dilationConstant A c d (u, v, w) = (A u + w, c • w, u + d • v) := rfl

@[simp] theorem dilationLinear_apply (A : V →ₗ[F] W) (u v : V) (w : W) :
    dilationLinear A (u, v, w) = (A u, -w, -v) := rfl

/-- The actual evaluation of the dilation pencil, with no spectral assumptions. -/
theorem dilation_evaluation (A0 A1 : V →ₗ[F] W) (c d t : F)
    (u v : V) (w : W) :
    (dilationConstant A0 c d + t • dilationLinear A1) (u, v, w) =
      ((A0 + t • A1) u + w, -(t - c) • w, u - (t - d) • v) := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, dilationConstant_apply,
    dilationLinear_apply, Prod.smul_mk, Prod.mk_add_mk]
  apply Prod.ext
  · module
  · apply Prod.ext <;> module

/-- Constant source embedding for a mixed constant-left/constant-right update. -/
def dilationEmbedding (R0 R1 : V →ₗ[F] E) (L0 L1 : G →ₗ[F] W)
    (Z : V →ₗ[F] G) (c d : F) :
    (V × (V × W)) →ₗ[F] (((V × (V × W)) × E) × G) :=
  let u := LinearMap.fst F V (V × W)
  let v := (LinearMap.fst F V W).comp (LinearMap.snd F V (V × W))
  let w := (LinearMap.snd F V W).comp (LinearMap.snd F V (V × W))
  let core := u.prod (v.prod (w + (L0 + c • L1).comp (Z.comp u)))
  (core.prod (R1.comp u + (R0 + d • R1).comp v)).prod (Z.comp u)

/-- Constant target compression for the same update. -/
def dilationCompression (U : E →ₗ[F] W) (R0 R1 : V →ₗ[F] E)
    (L0 L1 : G →ₗ[F] W) (c d : F) :
    (((W × (W × V)) × E) × G) →ₗ[F] (W × (W × V)) :=
  let core := (LinearMap.fst F (W × (W × V)) E).comp
    (LinearMap.fst F ((W × (W × V)) × E) G)
  let f := (LinearMap.fst F W (W × V)).comp core
  let g := (LinearMap.fst F W V).comp ((LinearMap.snd F W (W × V)).comp core)
  let h := (LinearMap.snd F W V).comp ((LinearMap.snd F W (W × V)).comp core)
  let j := (LinearMap.snd F (W × (W × V)) E).comp
    (LinearMap.fst F ((W × (W × V)) × E) G)
  let k := LinearMap.snd F ((W × (W × V)) × E) G
  (f + U.comp j + L1.comp k + U.comp ((R0 + d • R1).comp h)).prod
    ((g + (L0 + c • L1).comp k).prod h)

@[simp] theorem dilationEmbedding_apply (R0 R1 : V →ₗ[F] E)
    (L0 L1 : G →ₗ[F] W) (Z : V →ₗ[F] G) (c d : F)
    (u v : V) (w : W) :
    dilationEmbedding R0 R1 L0 L1 Z c d (u, v, w) =
      (((u, v, w + (L0 + c • L1) (Z u)), R1 u + (R0 + d • R1) v), Z u) := rfl

@[simp] theorem dilationCompression_apply (U : E →ₗ[F] W)
    (R0 R1 : V →ₗ[F] E) (L0 L1 : G →ₗ[F] W) (c d : F)
    (f g : W) (h : V) (j : E) (k : G) :
    dilationCompression U R0 R1 L0 L1 c d (((f, g, h), j), k) =
      (f + U j + L1 k + U ((R0 + d • R1) h), g + (L0 + c • L1) k, h) := rfl

theorem dilationEmbedding_injective (R0 R1 : V →ₗ[F] E)
    (L0 L1 : G →ₗ[F] W) (Z : V →ₗ[F] G) (c d : F) :
    Function.Injective (dilationEmbedding R0 R1 L0 L1 Z c d) := by
  rintro ⟨u, v, w⟩ ⟨u', v', w'⟩ h
  have hu := congrArg (fun x => x.1.1.1) h
  have hv := congrArg (fun x => x.1.1.2.1) h
  have hw := congrArg (fun x => x.1.1.2.2) h
  change u = u' at hu
  change v = v' at hv
  change w + (L0 + c • L1) (Z u) = w' + (L0 + c • L1) (Z u') at hw
  rw [hu] at hw
  exact Prod.ext hu (Prod.ext hv (add_right_cancel hw))

theorem dilationCompression_surjective (U : E →ₗ[F] W)
    (R0 R1 : V →ₗ[F] E) (L0 L1 : G →ₗ[F] W) (c d : F) :
    Function.Surjective (dilationCompression U R0 R1 L0 L1 c d) := by
  rintro ⟨f, g, h⟩
  refine ⟨(((f - U ((R0 + d • R1) h), g, h), 0), 0), ?_⟩
  simp

/-- The two coefficient identities for the actual constant full-rank maps.
No eigenstructure, rank decomposition, distinctness of `c,d`, or genericity
hypothesis is needed for this algebraic embedding. -/
theorem dilation_compression_coefficients
    (B0 B1 C0 C1 : V →ₗ[F] W) (U : E →ₗ[F] W)
    (R0 R1 : V →ₗ[F] E) (L0 L1 : G →ₗ[F] W) (Z : V →ₗ[F] G)
    (h0 : B0 - C0 = U.comp R0 + L0.comp Z)
    (h1 : B1 - C1 = U.comp R1 + L1.comp Z)
    (c d : F) (i : Bool) :
    (dilationCompression U R0 R1 L0 L1 c d).comp
      ((((dilationFamily C0 C1 c d i).prodMap
        (scalarDilationFamily (E := E) d i)).prodMap
        (scalarDilationFamily (E := G) c i)).comp
          (dilationEmbedding R0 R1 L0 L1 Z c d)) = dilationFamily B0 B1 c d i := by
  apply LinearMap.ext
  rintro ⟨u, v, w⟩
  have hh0 := LinearMap.congr_fun h0 u
  have hh1 := LinearMap.congr_fun h1 u
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply] at hh0 hh1
  have hb0 : B0 u = C0 u + U (R0 u) + L0 (Z u) := by
    rw [eq_add_of_sub_eq hh0]
    abel
  have hb1 : B1 u = C1 u + U (R1 u) + L1 (Z u) := by
    rw [eq_add_of_sub_eq hh1]
    abel
  cases i <;>
    simp only [dilationFamily, scalarDilationFamily, Bool.false_eq_true, ite_false,
      ite_true, LinearMap.comp_apply, dilationEmbedding_apply, LinearMap.prodMap_apply,
      dilationConstant_apply, dilationLinear_apply, LinearMap.smul_apply,
      LinearMap.id_apply, dilationCompression_apply, LinearMap.add_apply, map_add,
      map_smul, map_neg, hb0, hb1]
  all_goals
    apply Prod.ext
    · module
    · apply Prod.ext <;> module

/-- Section 3.2 as an actual simultaneous compression of both coefficients. -/
theorem jointCompression_dilation_of_factorized_difference
    (B0 B1 C0 C1 : V →ₗ[F] W) (U : E →ₗ[F] W)
    (R0 R1 : V →ₗ[F] E) (L0 L1 : G →ₗ[F] W) (Z : V →ₗ[F] G)
    (h0 : B0 - C0 = U.comp R0 + L0.comp Z)
    (h1 : B1 - C1 = U.comp R1 + L1.comp Z) (c d : F) :
    MatCP1.JointCompression (dilationFamily B0 B1 c d)
      (fun i => ((dilationFamily C0 C1 c d i).prodMap
        (scalarDilationFamily (E := E) d i)).prodMap
        (scalarDilationFamily (E := G) c i)) := by
  exact ⟨dilationCompression U R0 R1 L0 L1 c d,
    dilationEmbedding R0 R1 L0 L1 Z c d,
    dilationCompression_surjective U R0 R1 L0 L1 c d,
    dilationEmbedding_injective R0 R1 L0 L1 Z c d,
    dilation_compression_coefficients B0 B1 C0 C1 U R0 R1 L0 L1 Z h0 h1 c d⟩

end MatCP1Converse

module

public import MatCP1Converse.ForwardAnchorSwap
public import MatCP1.Cancellation

@[expose] public section

namespace MatCP1Converse

section Composition

variable {F I VA WA VB WB VC WC : Type*} [Field F]
  [AddCommGroup VA] [Module F VA] [AddCommGroup WA] [Module F WA]
  [AddCommGroup VB] [Module F VB] [AddCommGroup WB] [Module F WB]
  [AddCommGroup VC] [Module F VC] [AddCommGroup WC] [Module F WC]

theorem forward_jointCompression_trans
    (A : I → VA →ₗ[F] WA) (B : I → VB →ₗ[F] WB) (C : I → VC →ₗ[F] WC)
    (hAB : MatCP1.JointCompression A B) (hBC : MatCP1.JointCompression B C) :
    MatCP1.JointCompression A C := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := hAB
  obtain ⟨R, S, hR, hS, hRS⟩ := hBC
  refine ⟨P.comp R, S.comp Q, hP.comp hR, hS.comp hQ, ?_⟩
  intro i
  calc
    (P.comp R).comp ((C i).comp (S.comp Q)) =
        P.comp ((R.comp ((C i).comp S)).comp Q) := rfl
    _ = P.comp ((B i).comp Q) := by rw [hRS i]
    _ = A i := hPQ i

end Composition

section UniqueFactors

variable {F I VA WA VB WB X Y Z T : Type*} [Field F]
  [AddCommGroup VA] [Module F VA] [AddCommGroup WA] [Module F WA]
  [AddCommGroup VB] [Module F VB] [AddCommGroup WB] [Module F WB]
  [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
  [AddCommGroup Z] [Module F Z] [AddCommGroup T] [Module F T]
  [Unique X] [Unique Y]

theorem forward_jointCompression_remove_unique_right
    (A : I → VA →ₗ[F] WA) (B : I → VB →ₗ[F] WB) (S : I → X →ₗ[F] Y)
    (h : MatCP1.JointCompression A (fun i => (B i).prodMap (S i))) :
    MatCP1.JointCompression A B := by
  let es := LinearEquiv.prodUnique (R := F) (M := VB) (M₂ := X)
  let et := LinearEquiv.prodUnique (R := F) (M := WB) (M₂ := Y)
  have h' := MatCP1.JointCompression.linearEquiv _ _ (LinearEquiv.refl F VA)
    (LinearEquiv.refl F WA) es et h
  convert h' using 1
  · rfl
  · funext i
    apply LinearMap.ext
    intro x
    rfl

theorem forward_jointCompression_remove_unique_middle
    (A : I → VA →ₗ[F] WA) (B : I → VB →ₗ[F] WB)
    (S : I → X →ₗ[F] Y) (H : I → Z →ₗ[F] T)
    (h : MatCP1.JointCompression A (fun i => ((B i).prodMap (S i)).prodMap (H i))) :
    MatCP1.JointCompression A (fun i => (B i).prodMap (H i)) := by
  let es := (LinearEquiv.prodUnique (R := F) (M := VB) (M₂ := X)).prodCongr
    (LinearEquiv.refl F Z)
  let et := (LinearEquiv.prodUnique (R := F) (M := WB) (M₂ := Y)).prodCongr
    (LinearEquiv.refl F T)
  have h' := MatCP1.JointCompression.linearEquiv _ _ (LinearEquiv.refl F VA)
    (LinearEquiv.refl F WA) es et h
  convert h' using 1
  · rfl
  · funext i
    apply LinearMap.ext
    intro x
    rfl

end UniqueFactors

section Forward

variable {F V W E G : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [AddCommGroup E] [Module F E] [AddCommGroup G] [Module F G]

theorem jointCompression_dilation_constant_left
    (B0 B1 C0 C1 : V →ₗ[F] W) (U : E →ₗ[F] W) (R0 R1 : V →ₗ[F] E)
    (h0 : B0 - C0 = U.comp R0) (h1 : B1 - C1 = U.comp R1) (c d : F) :
    MatCP1.JointCompression (dilationFamily B0 B1 c d)
      (fun i => (dilationFamily C0 C1 c d i).prodMap (scalarDilationFamily (E := E) d i)) := by
  have h := jointCompression_dilation_of_factorized_difference B0 B1 C0 C1 U R0 R1
    (0 : (Fin 0 → F) →ₗ[F] W) 0 (0 : V →ₗ[F] (Fin 0 → F))
    (by simpa using h0) (by simpa using h1) c d
  exact forward_jointCompression_remove_unique_right _ _ _ h

theorem jointCompression_dilation_constant_right
    (B0 B1 C0 C1 : V →ₗ[F] W) (L0 L1 : G →ₗ[F] W) (Z : V →ₗ[F] G)
    (h0 : B0 - C0 = L0.comp Z) (h1 : B1 - C1 = L1.comp Z) (c d : F) :
    MatCP1.JointCompression (dilationFamily B0 B1 c d)
      (fun i => (dilationFamily C0 C1 c d i).prodMap (scalarDilationFamily (E := G) d i)) := by
  have h := jointCompression_dilation_of_factorized_difference B0 B1 C0 C1
    (0 : (Fin 0 → F) →ₗ[F] W) (0 : V →ₗ[F] (Fin 0 → F)) 0 L0 L1 Z
    (by simpa using h0) (by simpa using h1) d c
  have hstep := forward_jointCompression_remove_unique_middle _ _ _ _ h
  have hstart := jointCompression_dilation_anchor_swap B0 B1 d c
  have hend := (jointCompression_dilation_anchor_swap C0 C1 c d).prodMap _ _
    (scalarDilationFamily (E := G) d)
  exact forward_jointCompression_trans _ _ _
    (forward_jointCompression_trans _ _ _ hstart hstep) hend

/-- The complete mixed-factor embedding with every added scalar block at the
same prescribed point `d`. It uses two compression steps and the universal
constant anchor swap; no intermediate spectral assumption is needed. -/
theorem jointCompression_dilation_same_anchor
    (B0 B1 C0 C1 : V →ₗ[F] W) (U : E →ₗ[F] W)
    (R0 R1 : V →ₗ[F] E) (L0 L1 : G →ₗ[F] W) (Z : V →ₗ[F] G)
    (h0 : B0 - C0 = U.comp R0 + L0.comp Z)
    (h1 : B1 - C1 = U.comp R1 + L1.comp Z) (c d : F) :
    MatCP1.JointCompression (dilationFamily B0 B1 c d)
      (fun i => ((dilationFamily C0 C1 c d i).prodMap
        (scalarDilationFamily (E := E) d i)).prodMap
        (scalarDilationFamily (E := G) d i)) := by
  let M0 := C0 + U.comp R0
  let M1 := C1 + U.comp R1
  have hleft := jointCompression_dilation_constant_left M0 M1 C0 C1 U R0 R1
    (by dsimp [M0]; abel) (by dsimp [M1]; abel) c d
  have hr0 : B0 - M0 = L0.comp Z := by
    dsimp [M0]
    calc
      B0 - (C0 + U.comp R0) = (B0 - C0) - U.comp R0 := by abel
      _ = L0.comp Z := by rw [h0]; abel
  have hr1 : B1 - M1 = L1.comp Z := by
    dsimp [M1]
    calc
      B1 - (C1 + U.comp R1) = (B1 - C1) - U.comp R1 := by abel
      _ = L1.comp Z := by rw [h1]; abel
  have hright := jointCompression_dilation_constant_right B0 B1 M0 M1 L0 L1 Z hr0 hr1 c d
  have hleft' := hleft.prodMap _ _ (scalarDilationFamily (E := G) d)
  exact forward_jointCompression_trans _ _ _ hright hleft'

end Forward

end MatCP1Converse

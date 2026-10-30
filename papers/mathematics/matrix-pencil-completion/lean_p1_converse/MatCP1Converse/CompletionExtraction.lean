module

public import MatCP1Converse.CompletionSchur
public import MatCP1Converse.CompletionRank
public import MatCP1Converse.LinearStrictCancellation

@[expose] public section

namespace MatCP1Converse

variable {F U V W : Type*} [Field F] [Infinite F]
  [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
  [FiniteDimensional F U] [FiniteDimensional F V] [FiniteDimensional F W]

/-- The complete fixed-factor extraction lemma at the centered parameter zero.
The inputs are actual coefficientwise constant strict-equivalence maps for an
arbitrary completion, together with equality of the evaluated corner ranks.
The conclusion supplies a constant perturbation of rank at most the number of
added rows/columns and actual constant equivalences of both pencil coefficients. -/
theorem completion_extract_centered
    (A0 A1 B0 B1 : U →ₗ[F] W)
    (M0 M1 : (U × V) →ₗ[F] (W × V))
    (P : (W × V) ≃ₗ[F] (W × V)) (Q : (U × V) ≃ₗ[F] (U × V))
    (hcorner0 : (LinearMap.fst F W V).comp (M0.comp (LinearMap.inl F U V)) = A0)
    (hcorner1 : (LinearMap.fst F W V).comp (M1.comp (LinearMap.inl F U V)) = A1)
    (hM0 : M0 = P.toLinearMap.comp ((B0.prodMap (0 : V →ₗ[F] V)).comp Q.toLinearMap))
    (hM1 : M1 = P.toLinearMap.comp ((B1.prodMap (LinearMap.id : V →ₗ[F] V)).comp Q.toLinearMap))
    (hRank : Module.finrank F (LinearMap.range A0) = Module.finrank F (LinearMap.range B0)) :
    ∃ (E : U →ₗ[F] W) (p : W ≃ₗ[F] W) (q : U ≃ₗ[F] U),
      Module.finrank F (LinearMap.range E) ≤ Module.finrank F V ∧
      A0 = p.toLinearMap.comp (B0.comp q.toLinearMap) ∧
      A1 - E = p.toLinearMap.comp (B1.comp q.toLinearMap) := by
  classical
  let X0 := (LinearMap.fst F W V).comp (M0.comp (LinearMap.inr F U V))
  let Y0 := (LinearMap.snd F W V).comp (M0.comp (LinearMap.inl F U V))
  let Z0 := (LinearMap.snd F W V).comp (M0.comp (LinearMap.inr F U V))
  have hblocks0 : M0 = (A0.coprod X0).prod (Y0.coprod Z0) := by
    simpa only [hcorner0] using completion_decompose M0
  have htotalrank : Module.finrank F (LinearMap.range ((A0.coprod X0).prod (Y0.coprod Z0))) =
      Module.finrank F (LinearMap.range A0) := by
    rw [← hblocks0, hM0, completion_finrank_range_equiv, completion_finrank_range_prod_zero]
    exact hRank.symm
  obtain ⟨Ln, Rn, hN0, hNcorner⟩ := completion_normalize_pair A0 X0 Y0 Z0 M1 htotalrank
  let N1 := Ln.toLinearMap.comp (M1.comp Rn.toLinearMap)
  have hcornerN : (LinearMap.fst F W V).comp (N1.comp (LinearMap.inl F U V)) = A1 := by
    simpa only [N1, LinearMap.comp_assoc, hcorner1] using hNcorner
  let Xn := (LinearMap.fst F W V).comp (N1.comp (LinearMap.inr F U V))
  let Yn := (LinearMap.snd F W V).comp (N1.comp (LinearMap.inl F U V))
  let Zn := (LinearMap.snd F W V).comp (N1.comp (LinearMap.inr F U V))
  have hblocks1 : N1 = (A1.coprod Xn).prod (Yn.coprod Zn) := by
    simpa only [hcornerN] using completion_decompose N1
  let Pn := P.trans Ln
  let Qn := Rn.trans Q
  have hn0 : A0.prodMap (0 : V →ₗ[F] V) =
      Pn.toLinearMap.comp ((B0.prodMap (0 : V →ₗ[F] V)).comp Qn.toLinearMap) := by
    rw [← hN0, ← hblocks0, hM0]
    rfl
  have hn1 : (A1.coprod Xn).prod (Yn.coprod Zn) =
      Pn.toLinearMap.comp ((B1.prodMap (LinearMap.id : V →ₗ[F] V)).comp Qn.toLinearMap) := by
    rw [← hblocks1]
    dsimp [N1]
    rw [hM1]
    rfl
  obtain ⟨S, T, hS, hT, hZg⟩ := completion_invertible_normalized_border
    A0 A1 B0 B1 Xn Yn Zn Pn Qn hn0 hn1
  let Xg := A1.comp S + Xn
  let Yg := T.comp A1 + Yn
  let Zg := (T.coprod LinearMap.id).comp
    (((A1.coprod Xn).prod (Yn.coprod Zn)).comp (S.prod LinearMap.id))
  obtain ⟨Lg, Rg, hG0, hG1⟩ := completion_graph_shear_pair A0 A1 Xn Yn Zn S T hS hT
  obtain ⟨E, Ls, Rs, hErank, hS0, hS1⟩ := completion_schur_split A0 A1 Xg Yg Zg hZg
  let Pf := (Pn.trans Lg).trans Ls
  let Qf := Rs.trans (Rg.trans Qn)
  have hf0 : Pf.toLinearMap.comp
      ((B0.prodMap (0 : V →ₗ[F] V)).comp Qf.toLinearMap) =
      A0.prodMap (0 : V →ₗ[F] V) := by
    change Ls.toLinearMap.comp
      ((Lg.toLinearMap.comp
        ((Pn.toLinearMap.comp ((B0.prodMap (0 : V →ₗ[F] V)).comp Qn.toLinearMap)).comp
          Rg.toLinearMap)).comp Rs.toLinearMap) = _
    rw [← hn0, hG0, hS0]
  have hf1 : Pf.toLinearMap.comp
      ((B1.prodMap (LinearMap.id : V →ₗ[F] V)).comp Qf.toLinearMap) =
      (A1 - E).prodMap (LinearMap.id : V →ₗ[F] V) := by
    change Ls.toLinearMap.comp
      ((Lg.toLinearMap.comp
        ((Pn.toLinearMap.comp ((B1.prodMap (LinearMap.id : V →ₗ[F] V)).comp Qn.toLinearMap)).comp
          Rg.toLinearMap)).comp Rs.toLinearMap) = _
    rw [← hn1, hG1]
    exact hS1
  obtain ⟨p, q, hpq⟩ := linear_strict_common_summand_cancellation
    (fun i : Bool => if i then A1 - E else A0)
    (fun i : Bool => if i then B1 else B0)
    (fun i : Bool => if i then (LinearMap.id : V →ₗ[F] V) else 0)
    Pf Qf (by intro i; cases i <;> assumption)
  exact ⟨E, p, q, hErank, (hpq false).symm, (hpq true).symm⟩

end MatCP1Converse

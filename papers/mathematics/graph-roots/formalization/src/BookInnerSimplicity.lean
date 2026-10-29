import BookInnerExistence
import BookOuterSimplicity

noncomputable section
namespace BookCompletion
open Set Filter Topology

theorem actual_simple_of_inner_factor (n : ℕ) (hn : 1 ≤ n) {t d : ℝ} {H : ℝ → ℝ}
    (ht : t ∈ Ioo 0 (1/2)) (hroot : (realPolynomial n).IsRoot (-t))
    (hfac : ∀ s ∈ Ioo 0 (1/2), normalized n s = (2-s)^n*H s)
    (hd : HasDerivAt H d t) (hdne : d ≠ 0) :
    (realPolynomial n).rootMultiplicity (-t) = 1 := by
  have ht2 : 2-t ≠ 0 := (inner_domain ht).2.1.ne'
  have hzero := (real_root_iff_normalized n hn ht.1).mp hroot
  rw [hfac t ht,mul_eq_zero] at hzero
  have hH0 : H t = 0 := hzero.resolve_left (pow_ne_zero n ht2)
  have hprod := (((hasDerivAt_id t).const_sub 2).pow n).mul hd
  have hprod' : HasDerivAt (fun s : ℝ => (2-s)^n*H s) ((2-t)^n*d) t := by
    simpa only [hH0,mul_zero,zero_add,id_eq] using hprod
  have hnear : normalized n =ᶠ[𝓝 t] (fun s : ℝ => (2-s)^n*H s) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hfac s hs
  have hnorm : HasDerivAt (normalized n) ((2-t)^n*d) t :=
    hprod'.congr_of_eventuallyEq hnear
  exact actual_simple_of_normalized_derivative n hn ht.1 hroot hnorm
    (mul_ne_zero (pow_ne_zero n ht2) hdne)

theorem inner_even_actual_simple (n : ℕ) (hn : 2 ≤ n) (he : Even n) {t : ℝ}
    (ht : t ∈ Ioo 0 (1/2)) (hroot : (realPolynomial n).IsRoot (-t)) :
    (realPolynomial n).rootMultiplicity (-t) = 1 := by
  apply actual_simple_of_inner_factor (H:=innerF n) n (by omega) ht hroot
    (fun s hs => normalized_even_inner_factor n he hs.1.ne' (inner_domain hs).2.1.ne')
    (hasDerivAt_innerF (n:=n) (by omega) ht)
  exact (innerFprime_neg hn ht).ne

theorem inner_odd_actual_simple (n : ℕ) (hn : 3 ≤ n) (ho : Odd n) {t : ℝ}
    (ht : t ∈ Ioo 0 (1/2)) (hroot : (realPolynomial n).IsRoot (-t)) :
    (realPolynomial n).rootMultiplicity (-t) = 1 := by
  obtain ⟨l,hl,r,hr,hlr,hGl,hGr⟩ := innerG_exists_two n hn ho
  have hzero := (inner_odd_root_iff n (by omega) ho ht).mp hroot
  have hclass := (innerG_zero_classification hn hl hr hlr hGl hGr ht).mp hzero
  have hsigns := innerG_root_derivative_signs hn hl hr hlr hGl hGr
  have hne : innerGprime n t ≠ 0 := by
    rcases hclass with rfl | rfl
    · exact hsigns.1.ne
    · exact hsigns.2.ne'
  exact actual_simple_of_inner_factor (H:=innerG n) n (by omega) ht hroot
    (fun s hs => normalized_odd_inner_factor n ho hs.1.ne' (inner_domain hs).2.1.ne')
    (hasDerivAt_innerG (n:=n) (by omega) ht) hne

theorem complex_simple_of_real_simple (n : ℕ) (x : ℝ)
    (hreal : (realPolynomial n).rootMultiplicity x = 1) :
    (complexPolynomial n).rootMultiplicity (x:ℂ) = 1 := by
  have heq := Polynomial.eq_rootMultiplicity_map (p:=realPolynomial n)
    (f:=Complex.ofRealHom) Complex.ofReal_injective x
  rw [map_realPolynomial] at heq
  exact heq.symm.trans hreal

theorem inner_even_complex_simple (n : ℕ) (hn : 2 ≤ n) (he : Even n) {t : ℝ}
    (ht : t ∈ Ioo 0 (1/2)) (hroot : (realPolynomial n).IsRoot (-t)) :
    (complexPolynomial n).rootMultiplicity ((-t:ℝ):ℂ) = 1 :=
  complex_simple_of_real_simple n (-t) (inner_even_actual_simple n hn he ht hroot)

theorem inner_odd_complex_simple (n : ℕ) (hn : 3 ≤ n) (ho : Odd n) {t : ℝ}
    (ht : t ∈ Ioo 0 (1/2)) (hroot : (realPolynomial n).IsRoot (-t)) :
    (complexPolynomial n).rootMultiplicity ((-t:ℝ):ℂ) = 1 :=
  complex_simple_of_real_simple n (-t) (inner_odd_actual_simple n hn ho ht hroot)

#print axioms actual_simple_of_inner_factor
#print axioms inner_even_actual_simple
#print axioms inner_odd_actual_simple
#print axioms complex_simple_of_real_simple
#print axioms inner_even_complex_simple
#print axioms inner_odd_complex_simple
end BookCompletion

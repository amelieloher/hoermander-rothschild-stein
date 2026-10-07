-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FreeTriangularLiftAtZero
public import RothschildStein.L1.TriangularRecenter
public import RothschildStein.L1.FreeSpanningNeighborhood
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- A spanning system at any base point has one polynomial triangular
lift of dimension equal to the formal rank. On a single open neighborhood,
its actual brackets are free and span; all vertical coefficients use only
preceding coordinates (BB Theorem 10.19 and Remark 10.18, pp. 493–494). -/
theorem exists_free_polynomial_triangular_lift {a s n : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω)
    (hspan : Submodule.span ℝ (range (fun I : BoundedWord a s p =>
      wordBracket X (boundedWordList I) x)) = ⊤) :
    ∃ m : ℕ, ∃ U : Opens (Fin (n+m) → ℝ),
      ∃ P : Fin a → Fin m → MvPolynomial (Fin (n+m)) ℝ,
        n+m = freeDimension a s p ∧ m = freeDimension a s p - n ∧
        joinPoint x (0 : Fin m → ℝ) ∈ U ∧
        (U : Set (Fin (n+m) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ)) ∧
        (∀ i l, ∀ j ∈ (P i l).vars, j.val < n+l.val) ∧
        (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) U) ∧
        ∀ ξ ∈ U, FreeAt p s (triangularLift X P) ξ ∧
          Submodule.span ℝ (range (fun I : BoundedWord a s p =>
            wordBracket (triangularLift X P) (boundedWordList I) ξ)) = ⊤ := by
  classical
  have hz : (0 : Fin n → ℝ) ∈ translatedDomain Ω x := by
    change 0+x ∈ Ω
    simpa only [zero_add] using hx
  have hs : Submodule.span ℝ (range (fun I : BoundedWord a s p =>
      wordBracket (translatedFields X x) (boundedWordList I) 0)) = ⊤ := by
    rw [translatedFields_word_span Ω X hX x 0 (by simpa only [zero_add] using hx)]
    simpa only [zero_add] using hspan
  obtain ⟨m,V,P,hd,hm,hzV,hP,hY,hf,_⟩ := exists_free_triangular_lift_at_zero
    (translatedDomain Ω x) (translatedFields X x) (translatedFields_contDiffOn Ω X hX x) hz hs
  let ξ₀ : Fin (n+m) → ℝ := joinPoint x 0
  let Q := recenteredLiftPolynomials P x
  let Y := triangularLift X Q
  have hEq : Y = translatedFields (triangularLift (translatedFields X x) P) (-ξ₀) :=
    triangularLift_recentered X P x
  let W := translatedDomain V (-ξ₀)
  have hzW : ξ₀ ∈ W := by
    change ξ₀ + -ξ₀ ∈ V
    simpa only [add_neg_cancel] using hzV
  have hYW : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) W := by
    rw [hEq]
    exact translatedFields_contDiffOn V _ hY (-ξ₀)
  have hfY : FreeAt p s Y ξ₀ := by
    rw [hEq,translatedFields_freeAt_iff V _ hY (-ξ₀) ξ₀
      (by simpa only [add_neg_cancel] using hzV)]
    simpa only [add_neg_cancel] using hf
  obtain ⟨U,hξU,hUW,hall⟩ := exists_free_spanning_neighborhood W Y hYW hzW hfY hd
  let B : Opens (Fin (n+m) → ℝ) :=
    ⟨basePoint ⁻¹' (Ω : Set (Fin n → ℝ)),
      by
        have hb : (basePoint (n := n) (m := m) : (Fin (n+m) → ℝ) → (Fin n → ℝ)) =
            P1.paddingBaseCLM n m := funext (fun ξ => (P1.paddingBaseCLM_apply n m ξ).symm)
        simpa only [hb] using Ω.isOpen.preimage (P1.paddingBaseCLM n m).continuous⟩
  refine ⟨m,U ⊓ B,Q,hd,hm,?_,?_,recenteredLiftPolynomials_vars P x hP,?_,?_⟩
  · refine ⟨hξU,?_⟩
    change basePoint (joinPoint x (0 : Fin m → ℝ)) ∈ Ω
    simpa only [← P1.paddingBaseCLM_apply,P1.paddingBaseCLM_join] using hx
  · intro ξ hξ
    exact hξ.2
  · intro i
    exact (hYW i).mono (fun ξ hξ => hUW hξ.1)
  · intro ξ hξ
    exact hall ξ hξ.1
end RothschildStein.L1

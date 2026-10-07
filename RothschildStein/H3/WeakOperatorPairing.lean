-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.DriftProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped BigOperators

/-- The sum of the weak drift and square jets represents the
fixed operator in its exact test-function pairing (BB p. 361). -/
theorem integral_sumSquaresWithDrift_weak_jets {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (u : (Fin n → ℝ) → ℝ)
    (g : Fin (q+1) → (Fin n → ℝ) → ℝ) (h : Fin q → (Fin n → ℝ) → ℝ)
    (hg : ∀ i, hasWeakWordDeriv X Ω [i] u (g i))
    (hh : ∀ i : Fin q, hasWeakWordDeriv X Ω [i.succ,i.succ] u (h i))
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (∫ x in (Ω : Set (Fin n → ℝ)), (g 0 x+∑ i, h i x)*ψ x) =
      ∫ x in (Ω : Set (Fin n → ℝ)), u x*sumSquaresWithDriftTranspose X ψ x := by
  have hb := S.integral_sumSquaresWithDrift_product X Ω hX u (fun _ => 1)
    contDiffOn_const g h hg hh ψ
  have hconst (V : (Fin n → ℝ) → (Fin n → ℝ)) :
      fieldDerivative V (fun _ => (1 : ℝ)) = fun _ => 0 := by
    funext x
    simp only [fieldDerivative,fderiv_const_apply,zero_apply]
  have hzero (V : (Fin n → ℝ) → (Fin n → ℝ)) :
      fieldDerivative V (fun _ => (0 : ℝ)) = fun _ => 0 := by
    funext x
    simp only [fieldDerivative,fderiv_const_apply,zero_apply]
  have hop : sumSquaresWithDrift X (fun _ => (1 : ℝ)) = fun _ => 0 := by
    funext x
    simp only [sumSquaresWithDrift,hconst,hzero,Finset.sum_const_zero,add_zero]
  simpa only [hop,hconst,mul_zero,zero_mul,mul_one,Finset.sum_const_zero,add_zero] using hb

end RothschildStein.H3

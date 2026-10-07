-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.P1

/-- The ordinary iterated derivative chain rule
for a linear pullback of a function smooth only on an open set. This avoids
assuming smoothness at the pole when estimating the Taylor remainder. -/
theorem iteratedFDeriv_comp_linear_of_contDiffOn
    {E F B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : E →L[ℝ] F) (f : F → B) (S : Set F) (hS : IsOpen S)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f S) (j : ℕ) (x : E) (hx : L x ∈ S) :
    iteratedFDeriv ℝ j (f ∘ L) x =
      (iteratedFDeriv ℝ j f (L x)).compContinuousLinearMap (fun _ => L) := by
  have hpre : IsOpen (L ⁻¹' S) := hS.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hf
    (hS.uniqueDiffOn (𝕜 := ℝ)) (hpre.uniqueDiffOn (𝕜 := ℝ)) hx (i := j) (by simp)
  rw [iteratedFDerivWithin_of_isOpen j hpre hx,
    iteratedFDerivWithin_of_isOpen j hS hx] at he
  exact he

/-- A contracting linear pullback cannot increase
the norm of any retained ordinary derivative on its smooth domain. -/
theorem norm_iteratedFDeriv_comp_linear_le_of_contDiffOn
    {E F B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (f : F → B) (S : Set F) (hS : IsOpen S)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f S) (j : ℕ) (x : E) (hx : L x ∈ S) :
    ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ := by
  rw [iteratedFDeriv_comp_linear_of_contDiffOn L f S hS hf j x hx]
  apply ((iteratedFDeriv ℝ j f (L x)).norm_compContinuousLinearMap_le (fun _ => L)).trans
  have hp : (∏ _ : Fin j, ‖L‖) ≤ 1 := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      pow_le_one₀ (norm_nonneg L) hL (n := j)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg _)

end RothschildStein.P1

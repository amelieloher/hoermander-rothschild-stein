-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ParabolicEnergyCurves
import Mathlib.Tactic

/-! # Independence of the parabolic test identity from gradient representatives -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Replacing the gradient on a product null set inside the cylinder preserves
both the integrability and the value of every smooth space-time test identity. -/
theorem SatisfiesParabolicTestIdentity.congr_gradient {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g h : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (ht : SatisfiesParabolicTestIdentity X a I U u g)
    (he : ∀ i, (fun z : ℝ × (Fin N → ℝ) => g i z.1 z.2) =ᵐ[
      volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))]
        (fun z => h i z.1 z.2)) :
    SatisfiesParabolicTestIdentity X a I U u h := by
  intro φ hφ hc hs
  obtain ⟨hi, hid⟩ := ht φ hφ hc hs
  have hrep : (fun z : ℝ × (Fin N → ℝ) =>
      -(u z.1 z.2 * fderiv ℝ φ z (1, 0)) +
        ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 * fderiv ℝ φ z (0, X i z.2)) =ᵐ[volume]
      (fun z => -(u z.1 z.2 * fderiv ℝ φ z (1, 0)) +
        ∑ i, ∑ j, a z.1 z.2 i j * h j z.1 z.2 * fderiv ℝ φ z (0, X i z.2)) := by
    filter_upwards [ae_all_iff.mpr (fun i => ae_imp_of_ae_restrict (he i))] with z hz
    by_cases hm : z ∈ (I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))
    · simp only [fun i => hz i hm]
    · have hn : z ∉ tsupport φ := fun h => hm (hs h)
      simp only [fderiv_of_notMem_tsupport ℝ hn, zero_apply, mul_zero, neg_zero,
        Finset.sum_const_zero, add_zero]
  exact ⟨hi.congr hrep, (integral_congr_ae hrep).symm.trans hid⟩

end HeatKernel

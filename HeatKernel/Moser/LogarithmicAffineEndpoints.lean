-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicReciprocalTest
public import HeatKernel.Moser.WeakSolutionAffineIntegrals
import Mathlib.Tactic

/-! # Logarithmic endpoint identities with the linear correction restored -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- On a localization plateau, the corrected reciprocal energy is the weighted
logarithm of the original local value, including its constant normalization. -/
theorem WeakSolutionSpatialWeight.reciprocal_affineEnergy_eq_integral_of_plateau {N q : ℕ}
    {V : TopologicalSpace.Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) {c : ℝ} (hc : 0 < c)
    (w : zeroBoundaryGraph V X)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    {u φ : (Fin N → ℝ) → ℝ} (z : zeroBoundaryGraph V X)
    (hval : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] fun x => u x * φ x)
    (hplateau : ∀ x, W.toFun x ≠ 0 → φ x = 1)
    (hupos : ∀ᵐ x ∂volume, W.toFun x ≠ 0 → 0 ≤ u x) :
    W.affineEnergy (shiftedRpowWeakSolutionTest hc (p := -1) (by norm_num)) w c⁻¹ z =
      ∫ x, W.toFun x * (Real.log (u x + c) - Real.log c) := by
  rw [W.affineEnergy_eq_integral_of_plateau _ w c⁻¹ hw z hval hplateau]
  apply integral_congr_ae
  filter_upwards [hupos] with x hx
  by_cases hW : W.toFun x = 0
  · simp only [hW, zero_mul]
  · rw [shiftedReciprocalWeakSolutionTest_primitive hc (hx hW)]
    ring

end HeatKernel

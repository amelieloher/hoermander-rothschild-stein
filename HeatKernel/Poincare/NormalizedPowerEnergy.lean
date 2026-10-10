-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! Finite normalized vertex energies and their exact power identities. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped NNReal ENNReal

namespace HeatKernel

/-- A finite nonnegative energy and a positive finite volume determine a finite
normalized cost, whose pth power pays exactly the original energy. -/
theorem exists_normalized_power_energy {I V : ℝ≥0∞} (hI : I ≠ ⊤)
    (hV0 : V ≠ 0) (hVtop : V ≠ ⊤) {p : ℝ} (hp : 0 < p) :
    ∃ h : ℝ≥0, (h : ℝ≥0∞) = (I / V) ^ (1 / p) ∧
      V * (h : ℝ≥0∞) ^ p = I ∧ I ^ (1 / p) = V ^ (1 / p) * h := by
  have hdiv : I / V ≠ ⊤ := ENNReal.div_ne_top hI hV0
  have hroot : (I / V) ^ (1 / p) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hp.le) hdiv
  let h := ((I / V) ^ (1 / p)).toNNReal
  have he : (h : ℝ≥0∞) = (I / V) ^ (1 / p) := ENNReal.coe_toNNReal hroot
  have hcancel : V * (I / V) = I := by
    rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel hV0 hVtop, mul_one]
  refine ⟨h, he, ?_, ?_⟩
  · rw [he, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one, hcancel]
  · rw [he, ← ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le), hcancel]

end HeatKernel

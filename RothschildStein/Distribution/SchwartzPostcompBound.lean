-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.Distribution

/-- real and imaginary projections preserve
finite unweighted derivative bounds with their operator norms. -/
theorem schwartzSeminorm_postcomp_le {N : ℕ} (L : ℂ →L[ℝ] ℝ)
    (n : ℕ) (φ : SchwartzMap (Fin N → ℝ) ℂ) :
    SchwartzMap.seminorm ℝ 0 n (SchwartzMap.postcompCLM L φ) ≤
      ‖L‖ * SchwartzMap.seminorm ℝ 0 n φ := by
  apply SchwartzMap.seminorm_le_bound ℝ 0 n _ (by positivity)
  intro x
  simp only [pow_zero, one_mul]
  change ‖iteratedFDeriv ℝ n (L ∘ φ) x‖ ≤ _
  exact (L.norm_iteratedFDeriv_comp_left (φ.smooth (⊤ : ℕ∞)).contDiffAt (by simp)).trans
    (mul_le_mul_of_nonneg_left (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ φ n x) (norm_nonneg _))

end RothschildStein.Distribution

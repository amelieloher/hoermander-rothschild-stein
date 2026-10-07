-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactDerivativeMean

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Function
namespace RothschildStein.S
variable {n : ℕ}

/-- Directional derivatives of a compact smooth function
are integrable, so transfer-kernel sums can be integrated termwise
(BB pp. 76–78). -/
theorem integrable_compact_fderiv_apply {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcf : HasCompactSupport f) (v : Fin n → ℝ) :
    Integrable (fun x => fderiv ℝ f x v) volume := by
  have hc : HasCompactSupport (fun x => fderiv ℝ f x v) := by
    simpa only [Function.comp_def] using
      (hcf.fderiv ℝ).comp_left (g := fun A : (Fin n → ℝ) →L[ℝ] ℝ => A v) (by rfl)
  exact ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport hc

end RothschildStein.S

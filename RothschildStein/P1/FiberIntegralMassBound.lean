-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiberIntegralSupport
public import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1

/-- Fiber integration is bounded by fiber volume times the
uniform norm, with the support set and constant fixed independently
of the base point. -/
theorem norm_fiberIntegral_le {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {F : ((Fin n → ℝ) × (Fin d → ℝ)) → B}
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) {C : ℝ}
    (hsupp : ∀ x z, z ∉ K → F (x, z) = 0)
    (hbound : ∀ x z, z ∈ K → ‖F (x, z)‖ ≤ C) (x : Fin n → ℝ) :
    ‖∫ z, F (x, z)‖ ≤ volume.real K * C := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (hsupp x)]
  simpa only [mul_comm] using
    norm_setIntegral_le_of_norm_le_const hK.measure_lt_top (hbound x)

end RothschildStein.P1

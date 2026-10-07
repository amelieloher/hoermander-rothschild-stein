-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiberIntegralSupport
public import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1

/-- A continuous compactly supported family has one integrable
fiber majorant, uniform in the base point. This also applies to its
partial derivatives and supplies differentiation under the integral. -/
theorem exists_integrable_fiberMajorant {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B]
    {F : ((Fin n → ℝ) × (Fin d → ℝ)) → B}
    (hF : Continuous F) (hFc : HasCompactSupport F) :
    ∃ b : (Fin d → ℝ) → ℝ, Integrable b ∧ ∀ x z, ‖F (x, z)‖ ≤ b z := by
  classical
  obtain ⟨C, hC⟩ := hFc.exists_bound_of_continuous hF
  let K : Set (Fin d → ℝ) := Prod.snd '' tsupport F
  have hK : IsCompact K := hFc.isCompact.image continuous_snd
  refine ⟨K.indicator (fun _ => C), ?_, ?_⟩
  · exact (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
  · intro x z
    by_cases hz : z ∈ K
    · simpa only [indicator_of_mem hz] using hC (x, z)
    · have hf : F (x, z) = 0 := by
        by_contra h
        exact hz ⟨(x, z), subset_tsupport F h, rfl⟩
      simp only [indicator_of_notMem hz, hf, norm_zero, le_refl]

end RothschildStein.P1

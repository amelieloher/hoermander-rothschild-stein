-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependencePicardContraction

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter Function ODE
open scoped Topology NNReal

namespace RothschildStein.G1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Solve the linear variational equation on any bounded
time interval. The factorial Picard estimate supplies the fixed point
without a smallness condition on the interval (BB Proposition 1.2, p. 3). -/
theorem exists_linear_integralCurve_on_Icc
    {T : ℝ} (hT : 0 ≤ T) (A : ℝ → E →L[ℝ] E)
    (hc : ContinuousOn A (Icc (-T) T)) {K : ℝ≥0}
    (hb : ∀ t ∈ Icc (-T) T, ‖A t‖ ≤ K) (w₀ : E) :
    ∃ W : ℝ → E, Continuous W ∧ W 0 = w₀ ∧
      ∀ t ∈ Icc (-T) T, HasDerivWithinAt W (A t (W t)) (Icc (-T) T) t := by
  obtain ⟨n, C, hC⟩ := linearPicard_exists_contracting_iterate hT A hc hb w₀
  let γ := hC.fixedPoint
  have hγ : IsFixedPt (linearPicard hT A hc w₀) γ := hC.isFixedPt_fixedPoint_iterate
  let W := extendedCurve hT γ
  have heq : ∀ t ∈ Icc (-T) T,
      W t = picard (fun s w => A s w) 0 w₀ W t := by
    intro t ht
    calc
      W t = γ ⟨t, ht⟩ := extendedCurve_apply hT γ ht
      _ = linearPicard hT A hc w₀ γ ⟨t, ht⟩ := congrArg (fun η => η ⟨t, ht⟩) hγ.symm
      _ = picard (fun s w => A s w) 0 w₀ W t := rfl
  have hf : ContinuousOn (fun p : ℝ × E => A p.1 p.2) (Icc (-T) T ×ˢ univ) :=
    (hc.comp continuous_fst.continuousOn (fun _ hp => hp.1)).clm_apply continuous_snd.continuousOn
  refine ⟨W, extendedCurve_continuous hT γ, ?_, fun t ht => ?_⟩
  · simpa only [picard_apply₀] using heq 0 ⟨by linarith, hT⟩
  · exact (hasDerivWithinAt_picard_Icc ⟨by linarith, hT⟩ hf
      (extendedCurve_continuous hT γ).continuousOn (fun _ _ => mem_univ _) w₀ ht).congr_of_mem heq ht

end RothschildStein.G1

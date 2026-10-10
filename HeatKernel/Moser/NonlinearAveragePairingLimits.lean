-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.RepresentativeDualPairingLimits
public import HeatKernel.Bridge.HilbertDualTimeAverages
public import HeatKernel.Form.TimeAverageCompositionLimits

/-! # Strong local limits of flux pairings with nonlinear energy tests -/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology NNReal

namespace HeatKernel

/-- A continuous nonlinear energy test with linear growth can be paired with literal
forward time averages of a dual flux, with convergence on every compact interior time set. -/
theorem tendsto_integral_forwardTimeAverage_dual_comp {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {I K : Set ℝ} (hI : IsOpen I) (hK : IsCompact K) (hKI : K ⊆ I)
    {v : ℝ → E} {F : ℝ → (E →L[ℝ] ℝ)}
    (hv : MemLp v 2 (volume.restrict I)) (hF : MemLp F 2 (volume.restrict I))
    {P : E → E} (hP : Continuous P) {C : ℝ≥0} (hb : ∀ z, ‖P z‖ ≤ C * ‖z‖) :
    Tendsto (fun h => ∫ t in K, forwardTimeAverage h F t (P (forwardTimeAverage h v t)))
      (𝓝[>] 0) (𝓝 (∫ t in K, F t (P (v t)))) := by
  let : InnerProductSpace ℝ (E →L[ℝ] ℝ) := hilbertDualInnerProductSpace E
  have hFm := (eventually_memLp_timeAverages_restrict hI hK hKI hF).mono fun _ hh => hh.1
  have hvm := (eventually_memLp_timeAverages_restrict hI hK hKI hv).mono fun _ hh => hh.1
  have hvK := hv.mono_measure (Measure.restrict_mono_set volume hKI)
  exact tendsto_integral_dual_apply_of_eventually_memLp hFm
    (hvm.mono fun _ hh => memLp_comp_of_continuous_norm_le hP hb hh)
    (hF.mono_measure (Measure.restrict_mono_set volume hKI))
    (memLp_comp_of_continuous_norm_le hP hb hvK)
    (tendsto_eLpNorm_forwardTimeAverage_sub_restrict hI hK hKI hF)
    (tendsto_eLpNorm_comp_forwardTimeAverage_sub_restrict hP hb hI hK hKI hv)

end HeatKernel

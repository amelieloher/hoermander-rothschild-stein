-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.CriticalKernelFarBound
public import RothschildStein.H1.PrincipalValueTruncatedIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The nonsingular far term is continuous. A common
compact support on each parameter ball supplies a local dominator
(BB Proposition 6.29, p. 277). -/
theorem continuous_principalValue_far
    {ν F ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x)
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
    Continuous (principalValueFar G ν F ψ) := by
  obtain ⟨CF, hCF, hFb⟩ := exists_criticalKernel_far_bound G hν hF hhom
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuous hc
  let Cψ := max B 0
  have hCψ : 0 ≤ Cψ := le_max_right _ _
  have hψb (y : Fin N → ℝ) : ‖ψ y‖ ≤ Cψ := (hB y).trans (le_max_left _ _)
  apply continuous_iff_continuousAt.mpr
  intro x₀
  obtain ⟨K, hK, hvanish⟩ := exists_commonTranslatedSupport G hs x₀
  let D := K.indicator (fun _ => CF * Cψ)
  have hiD : Integrable D volume := (integrable_indicator_iff hK.measurableSet).mpr
    (continuousOn_const.integrableOn_compact hK)
  change ContinuousAt (fun x => ∫ w in {w | 1 ≤ ν w}, F w * ψ (G.mul x (G.inv w))) x₀
  apply continuousAt_of_dominated (bound := D)
  · exact Eventually.of_forall fun x =>
      (integrableOn_principalValue_far G hν hF hc hs x).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1)] with x hx
    filter_upwards [ae_restrict_mem (isClosed_le continuous_const hν.1).measurableSet] with w hw
    change ‖F w * ψ (G.mul x (G.inv w))‖ ≤ K.indicator (fun _ => CF * Cψ) w
    by_cases hwK : w ∈ K
    · rw [indicator_of_mem hwK, norm_mul]
      exact mul_le_mul (hFb w hw) (hψb _) (norm_nonneg _) hCF
    · rw [indicator_of_notMem hwK, hvanish x hx w hwK, mul_zero, norm_zero]
  · exact hiD.mono_measure Measure.restrict_le_self
  · exact Eventually.of_forall fun w => (continuous_const.mul
      (hc.comp ((G2.continuous_mul G).comp (continuous_id.prodMk continuous_const)))).continuousAt

end RothschildStein.H1

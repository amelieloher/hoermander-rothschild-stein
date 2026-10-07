-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PrincipalValueNearBound
public import RothschildStein.G2.PowerBochner

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The subtracted critical kernel is absolutely
integrable near zero, for every base point (BB Prop 6.29, p. 277). -/
theorem integrableOn_principalValue_near
    {ν F ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x)
    (hc : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) (x : Fin N → ℝ) :
    IntegrableOn (fun w => F w * (ψ (G.mul x (G.inv w)) - ψ x)) {w | ν w ≤ 1} volume := by
  obtain ⟨C, hC, hb⟩ := exists_principalValue_near_bound G hν hF hhom hc hs
  have hp : IntegrableOn (fun w => (ν w) ^ (1 - (G.homogeneousDimension : ℝ)))
      {w | ν w ≤ 1} volume := by
    have hi := (G2.integrableOn_power_near_iff hν
      ((G.homogeneousDimension : ℝ) - 1) (by norm_num : (0 : ℝ) < 1)).mpr (by linarith)
    have he : -((G.homogeneousDimension : ℝ) - 1) = 1 - (G.homogeneousDimension : ℝ) := by ring
    simpa only [he] using hi
  have hFm : StronglyMeasurable F := hF.stronglyMeasurable_of_countable_compl (by simp)
  have hD : Continuous (fun w => ψ (G.mul x (G.inv w)) - ψ x) :=
    (hc.continuous.comp ((G2.continuous_mul G).comp
      (continuous_const.prodMk (G2.continuous_inv G)))).sub continuous_const
  apply (hp.const_mul C).mono' ((hFm.mul hD.stronglyMeasurable).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
  filter_upwards [ae_restrict_mem (isClosed_le hν.1 continuous_const).measurableSet] with w hw
  change ‖F w * (ψ (G.mul x (G.inv w)) - ψ x)‖ ≤ C * (ν w) ^ (1 - (G.homogeneousDimension : ℝ))
  exact hb x w hw

end RothschildStein.H1

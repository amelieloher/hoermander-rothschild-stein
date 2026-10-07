-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PrincipalValueNearIntegrability
public import RothschildStein.H1.PrincipalValueDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The subtracted near term is continuous by a single
integrable gauge-power dominator, uniformly in the base point
(BB Proposition 6.29, pp. 276–278). -/
theorem continuous_principalValue_near
    {ν F ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x)
    (hc : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) :
    Continuous (principalValueNear G ν F ψ) := by
  obtain ⟨C, _, hb⟩ := exists_principalValue_near_bound G hν hF hhom hc hs
  have hp : IntegrableOn (fun w => (ν w) ^ (1 - (G.homogeneousDimension : ℝ)))
      {w | ν w < 1} volume := by
    have hi := (G2.integrableOn_power_near_iff hν
      ((G.homogeneousDimension : ℝ) - 1) (by norm_num : (0 : ℝ) < 1)).mpr (by linarith)
    have he : -((G.homogeneousDimension : ℝ) - 1) = 1 - (G.homogeneousDimension : ℝ) := by ring
    have hi' : IntegrableOn (fun w => (ν w) ^ (1 - (G.homogeneousDimension : ℝ)))
        {w | ν w ≤ 1} volume := by simpa only [he] using hi
    exact hi'.mono_set (fun w (hw : ν w < 1) => hw.le)
  change Continuous (fun x => ∫ w in {w | ν w < 1}, F w * (ψ (G.mul x (G.inv w)) - ψ x))
  apply continuous_of_dominated (bound := fun w => C * (ν w) ^ (1 - (G.homogeneousDimension : ℝ)))
  · intro x
    exact ((integrableOn_principalValue_near G hν hF hhom hc hs x).mono_set
      (fun w (hw : ν w < 1) => hw.le)).aestronglyMeasurable
  · intro x
    filter_upwards [ae_restrict_mem (isOpen_lt hν.1 continuous_const).measurableSet] with w hw
    exact hb x w hw.le
  · exact hp.const_mul C
  · exact Eventually.of_forall fun w => continuous_const.mul
      ((hc.continuous.comp ((G2.continuous_mul G).comp
        (continuous_id.prodMk continuous_const))).sub hc.continuous)

end RothschildStein.H1

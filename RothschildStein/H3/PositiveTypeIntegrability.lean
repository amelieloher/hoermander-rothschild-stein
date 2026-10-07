-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.KernelSphereBound
public import RothschildStein.G2.PowerBochner

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
namespace RothschildStein.H3
open G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- Every positive-type kernel is locally integrable on the whole
coordinate carrier, with no upper restriction α<Q (BB p. 346). -/
theorem PositiveType.locallyIntegrable {α : ℝ} {T ν : (Fin N → ℝ) → ℝ}
    (hT : PositiveType G α T) (hν : G.IsHomogeneousGauge ν) :
    LocallyIntegrable T volume := by
  let : Nonempty (Fin N) := ⟨⟨0, G.dimension_pos⟩⟩
  have hp : LocallyIntegrable (fun x => (ν x) ^ (α - (G.homogeneousDimension : ℝ))) volume := by
    have he : -((G.homogeneousDimension : ℝ) - α) = α - (G.homogeneousDimension : ℝ) := by ring
    simpa only [he] using (locallyIntegrable_power_iff hν
      ((G.homogeneousDimension : ℝ) - α)).mpr (by linarith [hT.positive])
  have hbound := hT.kernelSphereBound_properties hν
  rw [locallyIntegrable_iff]
  intro K hK
  apply ((hp.integrableOn_isCompact hK).const_mul (kernelSphereBound ν T)).mono'
    (hT.stronglyMeasurable.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : Fin N → ℝ))] with x hx
  simpa only [Real.norm_eq_abs] using hbound.2.2 x hx

/-- On a closed origin-centered gauge ball the L1 mass has the
exact coefficient Λ_{T,0} Q m R^α/α (BB p. 346, G2 radial integration). -/
theorem PositiveType.integral_abs_ball_bound {α R : ℝ} {T ν : (Fin N → ℝ) → ℝ}
    (hT : PositiveType G α T) (hν : G.IsHomogeneousGauge ν) (hR : 0 < R) :
    (∫ x in {x | ν x ≤ R}, |T x|) ≤ kernelSphereBound ν T *
      ((G.homogeneousDimension : ℝ) * (volume {x | ν x < 1}).toReal * R ^ α / α) := by
  let : Nonempty (Fin N) := ⟨⟨0, G.dimension_pos⟩⟩
  have ht := (hT.locallyIntegrable hν).integrableOn_isCompact (isCompact_gauge_le hν R)
  have hp := (integrableOn_power_near_iff hν
    ((G.homogeneousDimension : ℝ) - α) hR).mpr (by linarith [hT.positive])
  have he : -((G.homogeneousDimension : ℝ) - α) = α - (G.homogeneousDimension : ℝ) := by ring
  have hmass := integral_mono_ae ht.norm (hp.const_mul (kernelSphereBound ν T)) (by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : Fin N → ℝ))] with x hx
    simpa only [Real.norm_eq_abs, he] using (hT.kernelSphereBound_properties hν).2.2 x hx)
  have hval := integral_power_near hν
    (by linarith [hT.positive] : (G.homogeneousDimension : ℝ) - α < G.homogeneousDimension) hR
  have hα : (G.homogeneousDimension : ℝ) - ((G.homogeneousDimension : ℝ) - α) = α := by ring
  simpa only [Real.norm_eq_abs, integral_const_mul, hval, hα] using hmass

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TransportMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal

/-- A probability average of measure-preserving transports is
 an Lp contraction for every finite p ≥ 1. -/
theorem transport_average_memLp_and_norm_le {α X : Type*}
    [MeasurableSpace α] [MeasurableSpace X]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure X) [SFinite ν]
    (T : α × X → X) (hT : Measurable T)
    (hpres : ∀ t, MeasurePreserving (fun x => T (t,x)) ν ν)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {f : X → ℝ} (hf : StronglyMeasurable f) (hfp : MemLp f p ν) :
    MemLp (fun x => ∫ t, f (T (t,x)) ∂μ) p ν ∧
      eLpNorm (fun x => ∫ t, f (T (t,x)) ∂μ) p ν ≤ eLpNorm f p ν := by
  have hp0 : p ≠ 0 := ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1).trans_le hp)
  have hpr : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hpt hp
  have hm : Integrable (fun x => |f x| ^ p.toReal) ν := by
    simpa only [Real.norm_eq_abs] using hfp.integrable_norm_rpow hp0 hpt
  obtain ⟨hmi,hmb⟩ := transport_average_moment_bound μ ν T hT hpres hpr hf hm
  have ha : AEStronglyMeasurable (fun x => ∫ t, f (T (t,x)) ∂μ) ν :=
    (hf.comp_measurable hT).aestronglyMeasurable.prod_swap.integral_prod_right'
  have hap : MemLp (fun x => ∫ t, f (T (t,x)) ∂μ) p ν :=
    (integrable_norm_rpow_iff ha hp0 hpt).mp (by simpa only [Real.norm_eq_abs] using hmi)
  refine ⟨hap,?_⟩
  rw [hap.eLpNorm_eq_integral_rpow_norm hp0 hpt,hfp.eLpNorm_eq_integral_rpow_norm hp0 hpt]
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow
  · exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  · simpa only [Real.norm_eq_abs] using hmb
  · exact inv_nonneg.mpr ENNReal.toReal_nonneg

end RothschildStein.H3

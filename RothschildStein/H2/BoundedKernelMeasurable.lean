-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.BoundedKernelAdjoint
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
/-- A bounded measurable kernel has a measurable integral action
on the finite patch. This supplies the outer measurability required by DCT. -/
theorem bounded_kernel_action_aestronglyMeasurable {μ : Measure X} {U : Set X}
    (hU : MeasurableSet U) (hμ : μ U < ⊤) {K : X → X → ℝ}
    (hK : Measurable (fun p : U × U => K p.1 p.2)) {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x ∈ U, ∀ y ∈ U, |K x y| ≤ M)
    {f : X → ℝ} (hf : Measurable (fun x : U => f x)) {F : ℝ} (_hF : 0 ≤ F)
    (hfb : ∀ x ∈ U, |f x| ≤ F) :
    AEStronglyMeasurable (fun x => ∫ y in U, K x y * f y ∂μ) (μ.restrict U) := by
  let ν : Measure U := μ.comap Subtype.val
  have hν : ν univ < ⊤ := by
    change (μ.comap Subtype.val) univ < ⊤
    rw [(MeasurableEmbedding.subtype_coe hU).comap_apply μ univ]
    simpa only [image_univ, Subtype.range_coe] using hμ
  let : IsFiniteMeasure ν := ⟨hν⟩
  have hm : Measurable (fun p : U × U => K p.1 p.2 * f p.2) := hK.mul (hf.comp measurable_snd)
  have hb : ∀ p : U × U, ‖K p.1 p.2 * f p.2‖ ≤ M * F := by
    intro p
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hbound _ p.1.property _ p.2.property) (hfb _ p.2.property) (abs_nonneg _) hM
  have hi : Integrable (fun p : U × U => K p.1 p.2 * f p.2) (ν.prod ν) :=
    memLp_one_iff_integrable.mp (MemLp.of_bound hm.aestronglyMeasurable (M * F) (ae_of_all _ hb))
  have ha : AEStronglyMeasurable (fun x : U => ∫ y in U, K x y * f y ∂μ) ν := by
    have hh := hi.integral_prod_left.aestronglyMeasurable
    have he : (fun x : U => ∫ y : U, K x y * f y ∂ν) =
        (fun x : U => ∫ y in U, K x y * f y ∂μ) := by
      funext x
      exact integral_subtype_comap (μ := μ) hU (fun y => K x y * f y)
    rw [he] at hh
    exact hh
  have he : AEStronglyMeasurable (fun x => ∫ y in U, K x y * f y ∂μ)
      (Measure.map Subtype.val ν) :=
    (MeasurableEmbedding.subtype_coe hU).aestronglyMeasurable_map_iff.mpr ha
  change AEStronglyMeasurable _ (Measure.map Subtype.val (μ.comap Subtype.val)) at he
  simpa only [map_comap_subtype_coe hU] using he

end RothschildStein.H2

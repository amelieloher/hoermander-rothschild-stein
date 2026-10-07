-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.TruncatedConvergence
public import RothschildStein.H2.TruncatedLimits

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Continuous Hölder input is ae strongly measurable on the input set. -/
theorem BoundedHolder.aestronglyMeasurable_restrict {δ : ℝ≥0} {G : Set X} {f : X → ℝ}
    {μ : Measure X} (hf : BoundedHolder δ G f) (hδ : 0 < δ) (hG : MeasurableSet G) :
    AEStronglyMeasurable f (μ.restrict G) := by
  have hm : AEStronglyMeasurable (fun y : G => f y) (μ.comap Subtype.val) :=
    (hf.measurable_subtype hδ).aestronglyMeasurable
  have he := (MeasurableEmbedding.subtype_coe hG).aestronglyMeasurable_map_iff.mpr hm
  simpa only [map_comap_subtype_coe hG] using he

/-- The principal value is the regularized integral plus the prescribed
T(1) limit. BB Theorem 7.12(c), p. 304. This proves existence and the formula;
the Hölder norm estimate is a separate assertion. -/
theorem SupportedKernel.principalValue_limit {D : LocDoubling X} {E G : Set X}
    {β ν A S R : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β ν A S R K)
    (d : TruncDist D) {δ : ℝ≥0} (hδ : 0 < δ) {f : X → ℝ}
    (hf : BoundedHolder δ G f) {x : X} (hx : x ∈ E) {h : ℝ}
    (hT1 : Tendsto (fun ε : ℝ => truncatedIntegral D.μ G d.d' K ε (fun _ => 1) x)
      (𝓝[>] 0) (𝓝 h)) :
    Tendsto (fun ε : ℝ => truncatedIntegral D.μ G d.d' K ε f x)
      (𝓝[>] 0) (𝓝 (regularizedIntegral D.μ G K f x + h * f x)) := by
  have hreg := (hK.regularized_absolute hδ hf hx).1
  have ht := tendsto_truncated_of_integrable d hK.kernel.measurable_E hK.sub_G
    (hK.sub_G (hK.sub_EG hx)) hreg
  have he := ht.add (hT1.mul_const (f x))
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεp : 0 < ε := hε
  have hi1 := (hK.truncated_absolute d hεp (f := fun _ => 1) aestronglyMeasurable_const
    (M := 1) (by norm_num) (ae_of_all _ (by intro y; norm_num)) hx).1
  have hir : IntegrableOn (fun y => K x y * (f y - f x))
      (G ∩ {y | ε < d.d' x y}) D.μ := hreg.mono_set inter_subset_left
  change (∫ y in G ∩ {y | ε < d.d' x y}, K x y * (f y - f x) ∂D.μ) +
    truncatedIntegral D.μ G d.d' K ε (fun _ => 1) x * f x = _
  simp only [truncatedIntegral, mul_one]
  rw [← integral_mul_const, ← integral_add hir (by simpa only [mul_one] using hi1.mul_const (f x))]
  congr 1
  funext y
  ring

end RothschildStein.H2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.CoverWeights
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators Classical

namespace RothschildStein.H2
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

def czWeighted (B : ι → Set X) (f : X → ℝ) (i : ι) (x : X) : ℝ :=
  f x * coverWeight B i x

def czAverage (μ : Measure X) (B : ι → Set X) (f : X → ℝ) (i : ι) : ℝ :=
  (∫ x, czWeighted B f i x ∂μ) / (μ (B i)).toReal

def czReplacement (μ : Measure X) (B : ι → Set X) (f : X → ℝ) (i : ι) : X → ℝ :=
  (B i).indicator (fun _ => czAverage μ B f i)

def czBad (μ : Measure X) (B : ι → Set X) (f : X → ℝ) (i : ι) (x : X) : ℝ :=
  czWeighted B f i x - czReplacement μ B f i x

theorem czWeighted_integrable (μ : Measure X) (B : ι → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (hfinite : ∀ x, {i | x ∈ B i}.Finite)
    (f : X → ℝ) (hf : Integrable f μ) (i : ι) : Integrable (czWeighted B f i) μ := by
  refine hf.mono (hf.aestronglyMeasurable.mul
    (measurable_coverWeight B hB i).aestronglyMeasurable) ?_
  filter_upwards [] with x
  obtain ⟨hw, hw1⟩ := coverWeight_nonneg_le_one B x (hfinite x) i
  change ‖f x * coverWeight B i x‖ ≤ ‖f x‖
  rw [norm_mul, Real.norm_of_nonneg hw]
  exact mul_le_of_le_one_right (norm_nonneg _) hw1

omit [Countable ι] in
theorem czBad_zero_off (μ : Measure X) (B : ι → Set X) (f : X → ℝ) (i : ι)
    {x : X} (hx : x ∉ B i) : czBad μ B f i x = 0 := by
  simp [czBad, czWeighted, coverWeight, czReplacement, hx]

omit [Countable ι] in
theorem czReplacement_integrable (μ : Measure X) (B : ι → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (hμ : ∀ i, μ (B i) ≠ ∞)
    (f : X → ℝ) (i : ι) : Integrable (czReplacement μ B f i) μ := by
  exact (integrableOn_const (hμ i)).integrable_indicator (hB i)

theorem czBad_integrable (μ : Measure X) (B : ι → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (hμ : ∀ i, μ (B i) ≠ ∞)
    (hfinite : ∀ x, {i | x ∈ B i}.Finite) (f : X → ℝ) (hf : Integrable f μ) (i : ι) :
    Integrable (czBad μ B f i) μ :=
  (czWeighted_integrable μ B hB hfinite f hf i).sub
    (czReplacement_integrable μ B hB hμ f i)

omit [Countable ι] in
theorem czReplacement_integral (μ : Measure X) (B : ι → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (hμ : ∀ i, μ (B i) ≠ ∞)
    (hpos : ∀ i, μ (B i) ≠ 0) (f : X → ℝ) (i : ι) :
    (∫ x, czReplacement μ B f i x ∂μ) = ∫ x, czWeighted B f i x ∂μ := by
  rw [czReplacement, integral_indicator_const _ (hB i)]
  simp only [smul_eq_mul, measureReal_def, czAverage]
  have hn : (μ (B i)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hpos i, hμ i⟩
  field_simp

theorem czBad_integral_zero (μ : Measure X) (B : ι → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (hμ : ∀ i, μ (B i) ≠ ∞)
    (hpos : ∀ i, μ (B i) ≠ 0) (hfinite : ∀ x, {i | x ∈ B i}.Finite)
    (f : X → ℝ) (hf : Integrable f μ) (i : ι) :
    (∫ x, czBad μ B f i x ∂μ) = 0 := by
  change (∫ x, czWeighted B f i x - czReplacement μ B f i x ∂μ) = 0
  rw [integral_sub (czWeighted_integrable μ B hB hfinite f hf i)
    (czReplacement_integrable μ B hB hμ f i),
    czReplacement_integral μ B hB hμ hpos f i, sub_self]

end RothschildStein.H2

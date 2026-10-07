-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.CZPieces
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators Classical

namespace RothschildStein.H2
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

omit [MeasurableSpace X] [Countable ι] in
theorem czWeighted_sum (B : ι → Set X) (hfinite : ∀ x, {i | x ∈ B i}.Finite)
    (f : X → ℝ) (x : X) :
    (∑' i, czWeighted B f i x) = (⋃ i, B i).indicator f x := by
  simp only [czWeighted, tsum_mul_left, coverWeight_sum B x (hfinite x)]
  by_cases hx : x ∈ ⋃ i, B i <;> simp [hx]

omit [MeasurableSpace X] [Countable ι] in
theorem czWeighted_nonneg (B : ι → Set X) (hfinite : ∀ x, {i | x ∈ B i}.Finite)
    (f : X → ℝ) {x : X} (hf : 0 ≤ f x) (i : ι) : 0 ≤ czWeighted B f i x :=
  mul_nonneg hf (coverWeight_nonneg_le_one B x (hfinite x) i).1

theorem czWeighted_mass_le (μ : Measure X) (B : ι → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (hfinite : ∀ x, {i | x ∈ B i}.Finite)
    (f : X → ℝ) (hf : Integrable f μ) :
    (∑' i, ∫⁻ x, ‖czWeighted B f i x‖ₑ ∂μ) ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := by
  rw [← lintegral_tsum (fun i => (czWeighted_integrable μ B hB hfinite f hf i).aemeasurable.enorm)]
  apply lintegral_mono
  intro x
  have hn : ∀ i, 0 ≤ czWeighted B (fun x => ‖f x‖) i x := fun i =>
    czWeighted_nonneg B hfinite (fun y => ‖f y‖) (x := x) (norm_nonneg (f x)) i
  have he : ∀ i, ‖czWeighted B f i x‖ₑ = ENNReal.ofReal (czWeighted B (fun x => ‖f x‖) i x) := by
    intro i
    rw [← ofReal_norm, czWeighted, norm_mul,
      Real.norm_of_nonneg (coverWeight_nonneg_le_one B x (hfinite x) i).1]
    rfl
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg hn]
  · rw [czWeighted_sum B hfinite]
    by_cases hx : x ∈ ⋃ i, B i
    · simp only [indicator_of_mem hx, ofReal_norm, le_refl]
    · simp [hx]
  · apply summable_of_hasFiniteSupport
    apply (hfinite x).subset
    intro i hi
    by_contra hnot
    change x ∉ B i at hnot
    exact hi (by simp [czWeighted, coverWeight, hnot])

omit [Countable ι] in
theorem czAverage_nonneg (μ : Measure X) (B : ι → Set X)
    (hfinite : ∀ x, {i | x ∈ B i}.Finite) (f : X → ℝ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (i : ι) : 0 ≤ czAverage μ B f i := by
  apply div_nonneg _ ENNReal.toReal_nonneg
  apply integral_nonneg_of_ae
  filter_upwards [hf] with x hx
  exact czWeighted_nonneg B hfinite f hx i

omit [Countable ι] in
theorem czReplacement_nonneg (μ : Measure X) (B : ι → Set X)
    (hfinite : ∀ x, {i | x ∈ B i}.Finite) (f : X → ℝ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (i : ι) (x : X) :
    0 ≤ czReplacement μ B f i x := by
  unfold czReplacement
  by_cases hx : x ∈ B i
  · simpa [hx] using czAverage_nonneg μ B hfinite f hf i
  · simp [hx]

theorem czReplacement_mass_eq (μ : Measure X) (B : ι → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (hμ : ∀ i, μ (B i) ≠ ∞)
    (hpos : ∀ i, μ (B i) ≠ 0) (hfinite : ∀ x, {i | x ∈ B i}.Finite)
    (f : X → ℝ) (hf : Integrable f μ) (hn : ∀ᵐ x ∂μ, 0 ≤ f x) (i : ι) :
    (∫⁻ x, ‖czReplacement μ B f i x‖ₑ ∂μ) = ∫⁻ x, ‖czWeighted B f i x‖ₑ ∂μ := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (czReplacement_integrable μ B hB hμ f i),
    ← ofReal_integral_norm_eq_lintegral_enorm (czWeighted_integrable μ B hB hfinite f hf i)]
  congr 1
  calc
    _ = ∫ x, czReplacement μ B f i x ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => Real.norm_of_nonneg (czReplacement_nonneg μ B hfinite f hn i x)
    _ = ∫ x, czWeighted B f i x ∂μ := czReplacement_integral μ B hB hμ hpos f i
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hn] with x hx
      exact (Real.norm_of_nonneg (czWeighted_nonneg B hfinite f hx i)).symm

theorem czBad_mass_le (μ : Measure X) (B : ι → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (hμ : ∀ i, μ (B i) ≠ ∞)
    (hpos : ∀ i, μ (B i) ≠ 0) (hfinite : ∀ x, {i | x ∈ B i}.Finite)
    (f : X → ℝ) (hf : Integrable f μ) (hn : ∀ᵐ x ∂μ, 0 ≤ f x) :
    (∑' i, ∫⁻ x, ‖czBad μ B f i x‖ₑ ∂μ) ≤ 2 * ∫⁻ x, ‖f x‖ₑ ∂μ := by
  calc
    _ ≤ ∑' i, ((∫⁻ x, ‖czWeighted B f i x‖ₑ ∂μ) +
        ∫⁻ x, ‖czReplacement μ B f i x‖ₑ ∂μ) := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [← lintegral_add_left' (czWeighted_integrable μ B hB hfinite f hf i).aemeasurable.enorm]
      apply lintegral_mono
      intro x
      exact enorm_sub_le
    _ = 2 * (∑' i, ∫⁻ x, ‖czWeighted B f i x‖ₑ ∂μ) := by
      simp_rw [czReplacement_mass_eq μ B hB hμ hpos hfinite f hf hn]
      rw [ENNReal.tsum_add, two_mul]
    _ ≤ _ := mul_le_mul' le_rfl (czWeighted_mass_le μ B hB hfinite f hf)

end RothschildStein.H2

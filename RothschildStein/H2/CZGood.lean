-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.CZMass

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators Classical

namespace RothschildStein.H2
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- The good part: original data away from the covering, replaced averages on it. -/
def czGood (μ : Measure X) (B : ι → Set X) (f : X → ℝ) (x : X) : ℝ :=
  (⋃ i, B i)ᶜ.indicator f x + ∑' i, czReplacement μ B f i x

omit [Countable ι] in
theorem czReplacement_finite_support (μ : Measure X) (B : ι → Set X)
    (hfinite : ∀ x, {i | x ∈ B i}.Finite) (f : X → ℝ) (x : X) :
    (fun i => czReplacement μ B f i x).HasFiniteSupport := by
  apply (hfinite x).subset
  intro i hi
  by_contra hn
  change x ∉ B i at hn
  exact hi (by simp [czReplacement, hn])

omit [MeasurableSpace X] [Countable ι] in
theorem czWeighted_finite_support (B : ι → Set X)
    (hfinite : ∀ x, {i | x ∈ B i}.Finite) (f : X → ℝ) (x : X) :
    (fun i => czWeighted B f i x).HasFiniteSupport := by
  apply (hfinite x).subset
  intro i hi
  by_contra hn
  change x ∉ B i at hn
  exact hi (by simp [czWeighted, coverWeight, hn])

omit [Countable ι] in
theorem czGood_decomposition (μ : Measure X) (B : ι → Set X)
    (hfinite : ∀ x, {i | x ∈ B i}.Finite) (f : X → ℝ) (x : X) :
    f x = czGood μ B f x + ∑' i, czBad μ B f i x := by
  change f x = ((⋃ i, B i)ᶜ.indicator f x + ∑' i, czReplacement μ B f i x) +
    ∑' i, (czWeighted B f i x - czReplacement μ B f i x)
  rw [(summable_of_hasFiniteSupport (czWeighted_finite_support B hfinite f x)).tsum_sub
    (summable_of_hasFiniteSupport (czReplacement_finite_support μ B hfinite f x)),
    czWeighted_sum B hfinite]
  by_cases hx : x ∈ ⋃ i, B i <;> simp only [Set.indicator, Set.mem_compl_iff, hx, not_true_eq_false, not_false_eq_true, ite_true, ite_false] <;> ring

theorem czReplacement_series_integrable (μ : Measure X) (B : ι → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (hμ : ∀ i, μ (B i) ≠ ∞)
    (hpos : ∀ i, μ (B i) ≠ 0) (hfinite : ∀ x, {i | x ∈ B i}.Finite)
    (f : X → ℝ) (hf : Integrable f μ) (hn : ∀ᵐ x ∂μ, 0 ≤ f x) :
    Integrable (fun x => ∑' i, czReplacement μ B f i x) μ := by
  have hsmeas : Measurable (fun x => ∑' i, czReplacement μ B f i x) :=
    Measurable.tsum fun i => measurable_const.indicator (hB i)
  refine ⟨hsmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    _ = ∑' i, ∫⁻ x, ‖czReplacement μ B f i x‖ₑ ∂μ := by
      rw [← lintegral_tsum (fun i => (czReplacement_integrable μ B hB hμ f i).aemeasurable.enorm)]
      apply lintegral_congr
      intro x
      have hp : ∀ i, 0 ≤ czReplacement μ B f i x := fun i => czReplacement_nonneg μ B hfinite f hn i x
      rw [← ofReal_norm, Real.norm_of_nonneg (tsum_nonneg hp),
        ENNReal.ofReal_tsum_of_nonneg hp
          (summable_of_hasFiniteSupport (czReplacement_finite_support μ B hfinite f x))]
      apply tsum_congr
      intro i
      rw [← ofReal_norm, Real.norm_of_nonneg (hp i)]
    _ ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := by
      simp_rw [czReplacement_mass_eq μ B hB hμ hpos hfinite f hf hn]
      exact czWeighted_mass_le μ B hB hfinite f hf
    _ < ∞ := hasFiniteIntegral_iff_enorm.mp hf.hasFiniteIntegral

theorem czGood_integrable (μ : Measure X) (B : ι → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (hμ : ∀ i, μ (B i) ≠ ∞)
    (hpos : ∀ i, μ (B i) ≠ 0) (hfinite : ∀ x, {i | x ∈ B i}.Finite)
    (f : X → ℝ) (hf : Integrable f μ) (hn : ∀ᵐ x ∂μ, 0 ≤ f x) :
    Integrable (czGood μ B f) μ :=
  (hf.indicator (MeasurableSet.iUnion hB).compl).add
    (czReplacement_series_integrable μ B hB hμ hpos hfinite f hf hn)

theorem czGood_integral (μ : Measure X) (B : ι → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (hμ : ∀ i, μ (B i) ≠ ∞)
    (hpos : ∀ i, μ (B i) ≠ 0) (hfinite : ∀ x, {i | x ∈ B i}.Finite)
    (f : X → ℝ) (hf : Integrable f μ) (hn : ∀ᵐ x ∂μ, 0 ≤ f x) :
    (∫ x, czGood μ B f x ∂μ) = ∫ x, f x ∂μ := by
  have hmass : (∑' i, ∫⁻ x, ‖czWeighted B f i x‖ₑ ∂μ) ≠ ∞ :=
    ne_of_lt ((czWeighted_mass_le μ B hB hfinite f hf).trans_lt
      (hasFiniteIntegral_iff_enorm.mp hf.hasFiniteIntegral))
  have hrep : (∑' i, ∫⁻ x, ‖czReplacement μ B f i x‖ₑ ∂μ) ≠ ∞ := by
    simpa only [czReplacement_mass_eq μ B hB hμ hpos hfinite f hf hn] using hmass
  change (∫ x, (⋃ i, B i)ᶜ.indicator f x + ∑' i, czReplacement μ B f i x ∂μ) = _
  rw [integral_add (hf.indicator (MeasurableSet.iUnion hB).compl)
    (czReplacement_series_integrable μ B hB hμ hpos hfinite f hf hn),
    integral_tsum (fun i => (czReplacement_integrable μ B hB hμ f i).aestronglyMeasurable) hrep]
  simp_rw [czReplacement_integral μ B hB hμ hpos f]
  rw [← integral_tsum (fun i => (czWeighted_integrable μ B hB hfinite f hf i).aestronglyMeasurable) hmass]
  simp_rw [czWeighted_sum B hfinite]
  rw [← integral_add (hf.indicator (MeasurableSet.iUnion hB).compl)
    (hf.indicator (MeasurableSet.iUnion hB))]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by by_cases hx : x ∈ ⋃ i, B i <;> simp only [Set.indicator, Set.mem_compl_iff, hx, not_true_eq_false, not_false_eq_true, ite_true, ite_false] <;> ring

end RothschildStein.H2

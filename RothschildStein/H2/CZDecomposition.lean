-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.CZAverage

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators Classical

namespace RothschildStein.H2
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- The quantitative decomposition conclusion for a fixed covering. -/
def CZDecompositionFacts (μ : Measure X) (B : ι → Set X) (f : X → ℝ) (C : ℝ)
    (g : X → ℝ) (b : ι → X → ℝ) : Prop :=
  Measurable g ∧ (∀ i, Measurable (b i)) ∧ Integrable g μ ∧
    (∀ i, Integrable (b i) μ) ∧
    (∀ᵐ x ∂μ, f x = g x + ∑' i, b i x) ∧
    (∀ᵐ x ∂μ, 0 ≤ g x ∧ g x ≤ C) ∧
    (∫ x, g x ∂μ) = ∫ x, f x ∂μ ∧
    (∀ i x, x ∉ B i → b i x = 0) ∧
    (∀ i, (∫ x, b i x ∂μ) = 0) ∧
    (∑' i, ∫⁻ x, ‖b i x‖ₑ ∂μ) ≤ 2 * ∫⁻ x, ‖f x‖ₑ ∂μ ∧
    (∀ x, (fun i => b i x).HasFiniteSupport) ∧
    (∀ s : Finset ι, ∀ᵐ x ∂μ, ‖∑ i ∈ s, b i x‖ ≤ f x + g x) ∧
    (∀ p : ℝ≥0∞, MemLp f p μ → ∀ i, MemLp (b i) p μ) ∧
    (∀ p : ℝ≥0∞, IsFiniteMeasure μ → MemLp g p μ)

/-- Construct the measurable CZ decomposition from a countable,
pointwise finite covering with bounded averages and overlap
(BB Thm 7.32, pp. 324–325). -/
theorem exists_cz_decomposition (μ : Measure X) (B : ι → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (hμ : ∀ i, μ (B i) ≠ ∞)
    (hpos : ∀ i, μ (B i) ≠ 0) (hfinite : ∀ x, {i | x ∈ B i}.Finite)
    (f : X → ℝ) (hf : Integrable f μ) (hn : ∀ᵐ x ∂μ, 0 ≤ f x)
    {L N L₀ : ℝ} (hL : 0 ≤ L) (hN : 0 ≤ N)
    (havg : ∀ i, (⨍⁻ x in B i, ‖f x‖ₑ ∂μ) ≤ ENNReal.ofReal L)
    (hoverlap : ∀ x, coverMultiplicity B x ≤ ENNReal.ofReal N)
    (hgood : ∀ᵐ x ∂μ, x ∉ ⋃ i, B i → f x ≤ L₀) :
    ∃ g b, CZDecompositionFacts μ B f (max L₀ (N * L)) g b := by
  have hg := czGood_integrable μ B hB hμ hpos hfinite f hf hn
  have hb : ∀ i, Integrable (czBad μ B f i) μ :=
    czBad_integrable μ B hB hμ hfinite f hf
  let g := hg.aestronglyMeasurable.mk (czGood μ B f)
  let b : ι → X → ℝ := fun i => (B i).indicator
    ((hb i).aestronglyMeasurable.mk (czBad μ B f i))
  have hgeq : czGood μ B f =ᵐ[μ] g := hg.aestronglyMeasurable.ae_eq_mk
  have hbeq : ∀ i, czBad μ B f i =ᵐ[μ] b i := by
    intro i
    filter_upwards [(hb i).aestronglyMeasurable.ae_eq_mk] with x hx
    by_cases hi : x ∈ B i
    · exact hx.trans (indicator_of_mem hi _).symm
    · rw [czBad_zero_off μ B f i hi]
      exact (indicator_of_notMem hi _).symm
  have hgi : Integrable g μ := hg.congr hgeq
  have hbi : ∀ i, Integrable (b i) μ := fun i => (hb i).congr (hbeq i)
  have hgn : ∀ᵐ x ∂μ, 0 ≤ g x ∧ g x ≤ max L₀ (N * L) := by
    filter_upwards [hgeq, czGood_nonneg μ B hfinite f hn,
      czGood_bound μ B hfinite f hL hN
        (fun i => czAverage_le_laverage_bound μ B hB hμ hpos hfinite f hf hL i (havg i))
        hoverlap hgood] with x hx hx0 hxC
    exact hx ▸ ⟨hx0, hxC⟩
  refine ⟨g, b, hg.aestronglyMeasurable.measurable_mk,
    (fun i => (hb i).aestronglyMeasurable.measurable_mk.indicator (hB i)),
    hgi, hbi, ?_, hgn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hgeq, ae_all_iff.mpr hbeq] with x hx hxi
    rw [← hx]
    simp_rw [← hxi]
    exact czGood_decomposition μ B hfinite f x
  · exact (integral_congr_ae hgeq.symm).trans (czGood_integral μ B hB hμ hpos hfinite f hf hn)
  · intro i x hx
    exact indicator_of_notMem hx _
  · intro i
    exact (integral_congr_ae (hbeq i).symm).trans (czBad_integral_zero μ B hB hμ hpos hfinite f hf i)
  · have he : ∀ i, (∫⁻ x, ‖b i x‖ₑ ∂μ) = ∫⁻ x, ‖czBad μ B f i x‖ₑ ∂μ := fun i =>
      lintegral_congr_ae ((hbeq i).symm.fun_comp fun x => ‖x‖ₑ)
    simp_rw [he]
    exact czBad_mass_le μ B hB hμ hpos hfinite f hf hn
  · intro x
    apply (hfinite x).subset
    intro i hi
    by_contra hx
    change x ∉ B i at hx
    exact hi (indicator_of_notMem hx _)
  · intro s
    filter_upwards [hgeq, ae_all_iff.mpr hbeq, czBad_partial_bound μ B hfinite f hn s]
      with x hx hxi hbound
    simpa only [← hx, ← hxi] using hbound
  · intro p hp i
    exact (memLp_congr_ae (hbeq i)).mp (czBad_memLp μ B hB hμ hfinite f hp i)
  · intro p hfin
    let : IsFiniteMeasure μ := hfin
    apply MemLp.of_bound hgi.aestronglyMeasurable (max L₀ (N * L))
    filter_upwards [hgn] with x hx
    simpa only [Real.norm_of_nonneg hx.1] using hx.2

end RothschildStein.H2

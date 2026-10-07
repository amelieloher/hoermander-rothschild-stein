-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.OperatorSeries
public import RothschildStein.H2.SeriesTailBound

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal BigOperators Classical Topology

namespace RothschildStein.H2
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- Summing the off-diagonal tails after an L² limit is
legitimate; the exceptional set is the union of the enlarged bad balls
(BB p. 320). -/
theorem operator_bad_series_l1_bound (μ : Measure X) (U : Set X)
    (T : Lp ℝ 2 (μ.restrict U) →L[ℝ] Lp ℝ 2 (μ.restrict U))
    (B : ι → Set X) (b : ι → X → ℝ) (hb : ∀ i, MemLp (b i) 2 (μ.restrict U))
    (v : X → ℝ) (hv : MemLp v 2 (μ.restrict U)) (s : ℕ → Finset ι)
    (hlim : Tendsto (fun n => eLpNorm (fun x => (∑ i ∈ s n, b i x) - v x) 2 (μ.restrict U))
      atTop (𝓝 0)) :
    (∫⁻ x in U \ ⋃ i, B i, ‖(T (hv.toLp v)) x‖ₑ ∂μ) ≤
      ∑' i, ∫⁻ x in U \ B i, ‖(T ((hb i).toLp (b i))) x‖ₑ ∂μ := by
  obtain ⟨ns, _, hae⟩ := operator_series_ae_subsequence (μ.restrict U) T b hb v hv s hlim
  have hsub : U \ ⋃ i, B i ⊆ U := sdiff_subset
  have hmeas : ∀ i, AEMeasurable (fun x => (T ((hb i).toLp (b i))) x)
      (μ.restrict (U \ ⋃ i, B i)) := fun i =>
    ((Lp.aestronglyMeasurable _).mono_measure (Measure.restrict_mono hsub le_rfl)).aemeasurable
  have hlimY := ae_restrict_of_ae_restrict_of_subset hsub hae
  calc
    _ ≤ ∑' i, ∫⁻ x in U \ ⋃ i, B i, ‖(T ((hb i).toLp (b i))) x‖ₑ ∂μ :=
      lintegral_limit_le_tsum_of_partial_sums (μ.restrict (U \ ⋃ i, B i))
        (fun i x => (T ((hb i).toLp (b i))) x) hmeas (fun n => s (ns n)) _ hlimY
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro i
      apply lintegral_mono' (Measure.restrict_mono ?_ le_rfl) le_rfl
      intro x hx
      exact ⟨hx.1, fun hxi => hx.2 (mem_iUnion.mpr ⟨i, hxi⟩)⟩

end RothschildStein.H2

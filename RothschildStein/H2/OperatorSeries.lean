-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal BigOperators Classical Topology

namespace RothschildStein.H2
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- Continuity of the L² operator and an a.e. subsequence justify
summing the images of the bad pieces (BB p. 320). -/
theorem operator_series_ae_subsequence (μ : Measure X)
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (b : ι → X → ℝ) (hb : ∀ i, MemLp (b i) 2 μ)
    (v : X → ℝ) (hv : MemLp v 2 μ) (s : ℕ → Finset ι)
    (hlim : Tendsto (fun n => eLpNorm (fun x => (∑ i ∈ s n, b i x) - v x) 2 μ)
      atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => ∑ i ∈ s (ns n), (T ((hb i).toLp (b i))) x)
        atTop (𝓝 ((T (hv.toLp v)) x)) := by
  let S : ℕ → Lp ℝ 2 μ := fun n => ∑ i ∈ s n, (hb i).toLp (b i)
  have hSeq : ∀ n, (S n : X → ℝ) =ᵐ[μ] fun x => ∑ i ∈ s n, b i x := by
    intro n
    filter_upwards [Lp.coeFn_finsetSum (s n) (fun i => (hb i).toLp (b i)),
      ae_all_iff.mpr (fun i => (hb i).coeFn_toLp)] with x hx hbi
    simpa only [Finset.sum_apply, hbi] using hx
  have hconv : Tendsto S atTop (𝓝 (hv.toLp v)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm S v hv).mpr
    apply hlim.congr
    intro n
    exact (eLpNorm_congr_ae ((hSeq n).sub EventuallyEq.rfl)).symm
  have hTconv := T.continuous.continuousAt.tendsto.comp hconv
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hTconv).exists_seq_tendsto_ae
  have hTseq : ∀ n, (T (S n) : X → ℝ) =ᵐ[μ]
      fun x => ∑ i ∈ s n, (T ((hb i).toLp (b i))) x := by
    intro n
    simp only [S, map_sum]
    filter_upwards [Lp.coeFn_finsetSum (s n) (fun i => T ((hb i).toLp (b i)))] with x hx
    simpa only [Finset.sum_apply] using hx
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae, ae_all_iff.mpr hTseq] with x hx hxi
  exact hx.congr (fun n => hxi (ns n))

end RothschildStein.H2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.CZDecomposition
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Order.Filter.AtTopBot.Finset

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal BigOperators Classical Topology

namespace RothschildStein.H2
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- The CZ partial sums converge in L² along an increasing
exhaustion of the countable index set (BB pp. 319–321). -/
theorem CZDecompositionFacts.partial_sums_l2 (μ : Measure X) [IsFiniteMeasure μ]
    {B : ι → Set X} {f g : X → ℝ} {b : ι → X → ℝ} {C : ℝ}
    (hcz : CZDecompositionFacts μ B f C g b) (hf : MemLp f 2 μ) :
    ∃ s : ℕ → Finset ι, Monotone s ∧ Tendsto s atTop atTop ∧
      Tendsto (fun n => eLpNorm (fun x => (∑ i ∈ s n, b i x) - (f x - g x)) 2 μ)
        atTop (𝓝 0) := by
  rcases hcz with ⟨_, _, hgi, hbi, hdecomp, _, _, _, _, _, hfinite, hdom, _, hgLp⟩
  have hg : MemLp g 2 μ := hgLp 2 inferInstance
  obtain ⟨s, hsmono, hs⟩ := exists_seq_monotone_tendsto_atTop_atTop (Finset ι)
  have hSmeas : ∀ n, AEStronglyMeasurable (fun x => ∑ i ∈ s n, b i x) μ := fun n =>
    (integrable_finsetSum (s n) (fun i hi => hbi i)).aestronglyMeasurable
  have hui : UnifIntegrable (fun n x => ∑ i ∈ s n, b i x) 2 μ := by
    apply (unifIntegrable_const (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num)
      (hf.add hg)).ae_mono hSmeas
    intro n
    filter_upwards [hdom (s n)] with x hx
    change ‖∑ i ∈ s n, b i x‖ₑ ≤ ‖f x + g x‖ₑ
    simp only [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hx.trans (by
      simpa only [Real.norm_eq_abs] using le_abs_self (f x + g x)))
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => ∑ i ∈ s n, b i x) atTop (𝓝 (f x - g x)) := by
    filter_upwards [hdecomp] with x hx
    have he : (∑' i, b i x) = f x - g x := by linarith [hx]
    rw [← he]
    exact (summable_of_hasFiniteSupport (hfinite x)).hasSum.comp hs
  exact ⟨s, hsmono, hs, tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    hSmeas (hf.sub hg) hui hlim⟩

end RothschildStein.H2

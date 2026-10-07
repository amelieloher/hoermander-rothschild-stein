-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompactFlowInterpolation
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory Filter
open scoped ENNReal Topology

/-- Lp convergence implies convergence of the extended Lp norms.
 This is continuity of the norm on the actual Lp quotient. -/
theorem eLpNorm_tendsto_of_lp_difference {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ k, MemLp (f k) p μ) (hg : MemLp g p μ)
    (hc : Tendsto (fun k => eLpNorm (f k - g) p μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k) p μ) atTop (𝓝 (eLpNorm g p μ)) := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mpr hc
  simpa only [Lp.enorm_toLp] using ht.enorm

/-- The interpolation inequality passes to an Lp jet approximation with
unchanged constants. The three convergence hypotheses concern the function
and its drift and horizontal Sobolev derivatives. -/
theorem interpolation_bound_of_lp_approximation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f g h : α → ℝ} {fn gn hn : ℕ → α → ℝ}
    (hf : MemLp f p μ) (hg : MemLp g p μ) (hh : MemLp h p μ)
    (hfn : ∀ k, MemLp (fn k) p μ) (hgn : ∀ k, MemLp (gn k) p μ)
    (hhn : ∀ k, MemLp (hn k) p μ)
    (hfc : Tendsto (fun k => eLpNorm (fn k-f) p μ) atTop (𝓝 0))
    (hgc : Tendsto (fun k => eLpNorm (gn k-g) p μ) atTop (𝓝 0))
    (hhc : Tendsto (fun k => eLpNorm (hn k-h) p μ) atTop (𝓝 0))
    (A B : ℝ) (hb : ∀ k, eLpNorm (gn k) p μ ≤
      ENNReal.ofReal A * eLpNorm (fn k) p μ + ENNReal.ofReal B * eLpNorm (hn k) p μ) :
    eLpNorm g p μ ≤ ENNReal.ofReal A * eLpNorm f p μ + ENNReal.ofReal B * eLpNorm h p μ := by
  have hF := eLpNorm_tendsto_of_lp_difference μ hp hfn hf hfc
  have hG := eLpNorm_tendsto_of_lp_difference μ hp hgn hg hgc
  have hH := eLpNorm_tendsto_of_lp_difference μ hp hhn hh hhc
  have hR := (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal A) hF (Or.inr ENNReal.ofReal_ne_top)).add
    (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal B) hH (Or.inr ENNReal.ofReal_ne_top))
  exact le_of_tendsto_of_tendsto hG hR (Eventually.of_forall hb)

end RothschildStein.H3

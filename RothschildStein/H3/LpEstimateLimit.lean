-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.InterpolationDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory Filter
open scoped ENNReal Topology

/-- A compact-test a priori inequality passes to the Lp limits
of the operator and derivative jets, with its constant unchanged
(BB Proposition 8.28, p. 360; density argument). -/
theorem lp_estimate_of_approximation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f g : α → ℝ} {fn gn : ℕ → α → ℝ}
    (hf : MemLp f p μ) (hg : MemLp g p μ)
    (hfn : ∀ k, MemLp (fn k) p μ) (hgn : ∀ k, MemLp (gn k) p μ)
    (hfc : Tendsto (fun k => eLpNorm (fn k-f) p μ) atTop (𝓝 0))
    (hgc : Tendsto (fun k => eLpNorm (gn k-g) p μ) atTop (𝓝 0))
    (C : ℝ) (hbound : ∀ k, eLpNorm (gn k) p μ ≤ ENNReal.ofReal C*eLpNorm (fn k) p μ) :
    eLpNorm g p μ ≤ ENNReal.ofReal C*eLpNorm f p μ := by
  have hF := eLpNorm_tendsto_of_lp_difference μ hp hfn hf hfc
  have hG := eLpNorm_tendsto_of_lp_difference μ hp hgn hg hgc
  have hR := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hF
    (Or.inr ENNReal.ofReal_ne_top)
  exact le_of_tendsto_of_tendsto hG hR (Eventually.of_forall hbound)

end RothschildStein.H3

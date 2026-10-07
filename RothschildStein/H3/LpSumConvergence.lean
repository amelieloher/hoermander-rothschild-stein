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
open scoped ENNReal Topology BigOperators

/-- Finite Lp convergence is preserved by adding two approximated functions. -/
theorem lp_difference_add_tendsto {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f g : α → ℝ} {fn gn : ℕ → α → ℝ}
    (hf : Tendsto (fun k => eLpNorm (fn k-f) p μ) atTop (𝓝 0))
    (hg : Tendsto (fun k => eLpNorm (gn k-g) p μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fn k+gn k-(f+g)) p μ) atTop (𝓝 0) := by
  have hb : ∀ k, eLpNorm (fn k+gn k-(f+g)) p μ ≤
      eLpNorm (fn k-f) p μ + eLpNorm (gn k-g) p μ := by
    intro k
    have he : fn k+gn k-(f+g) = (fn k-f)+(gn k-g) := by
      funext x
      simp only [Pi.add_apply,Pi.sub_apply]
      ring
    rw [he]
    exact eLpNorm_add_le hp
  have hsum : Tendsto (fun k => eLpNorm (fn k-f) p μ + eLpNorm (gn k-g) p μ)
      atTop (𝓝 0) := by simpa only [zero_add] using hf.add hg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) hb

/-- Finite sums of Lp jet approximations converge to the sum of their jets. -/
theorem lp_difference_finset_sum_tendsto {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) {p : ℝ≥0∞} (hp : 1 ≤ p) (s : Finset ι)
    (f : ι → α → ℝ) (fn : ι → ℕ → α → ℝ)
    (hf : ∀ i ∈ s, Tendsto (fun k => eLpNorm (fn i k-f i) p μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm ((∑ i ∈ s, fn i k)-(∑ i ∈ s, f i)) p μ)
      atTop (𝓝 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact lp_difference_add_tendsto μ hp (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HolderRationalCylinders

/-! Interior containment for the shifted cylinders used in oscillation comparison. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open Set Metric
namespace HeatKernel

/-- A nearby shifted center and later top time leave room for a comparison
cylinder of radius `15 * r / 32` inside the original backward cylinder. -/
theorem holder_comparison_cylinder_subset
    {α : Type*} [PseudoMetricSpace α] {x x₀ c : α} {t top τ r δ : ℝ}
    (hr : 0 < r) (hδ : δ < r / 64) (hx : dist x x₀ < r)
    (hc : dist x c < 2 * δ) (ht : top - r ^ 2 < t)
    (htτ : t < τ) (hτtop : τ ≤ top) :
    Ioo (τ - 4 * (15 * r / 32) ^ 2) τ ×ˢ ball c (2 * (15 * r / 32)) ⊆
      Ioo (top - 4 * r ^ 2) top ×ˢ ball x₀ (2 * r) := by
  intro z hz
  have htime : top - 4 * r ^ 2 < τ - 4 * (15 * r / 32) ^ 2 := by
    nlinarith [sq_pos_of_pos hr]
  refine ⟨⟨htime.trans hz.1.1, hz.1.2.trans_le hτtop⟩, ?_⟩
  have hzspace : dist z.2 c < 2 * (15 * r / 32) := hz.2
  have hcx : dist c x < 2 * δ := by simpa only [dist_comm] using hc
  have htri := (dist_triangle z.2 c x₀).trans (add_le_add le_rfl (dist_triangle c x x₀))
  change dist z.2 x₀ < 2 * r
  linarith

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HolderCylinderContainment

/-! Dyadic comparison scales and rational cylinders for nearby pairs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open Set Metric
namespace HeatKernel

/-- A nearby space-time pair has a common rational cylinder below a dyadic
comparison scale between sixteen and thirty-two times its separation.
The initial comparison cylinder is contained in the original domain. -/
theorem exists_dyadic_rational_cylinder_comparison
    {α : Type*} [PseudoMetricSpace α] (c : ℕ → α) (hc : DenseRange c)
    {x y x₀ : α} {t s top r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hδr : δ < r / 64) (hx : dist x x₀ < r) (ht : top - r ^ 2 < t)
    (htop : max t s < top) (htime : |t - s| ≤ δ ^ 2) (hspace : dist x y ≤ δ) :
    ∃ (n : ℕ) (τ ρ : ℚ) (i : ℕ),
      16 * δ ≤ (15 * r / 32) * (1 / 2 : ℝ) ^ n ∧
      (15 * r / 32) * (1 / 2 : ℝ) ^ n < 32 * δ ∧
      4 * δ < (ρ : ℝ) ∧ (ρ : ℝ) < (15 * r / 32) * (1 / 2 : ℝ) ^ n ∧
      (t, x) ∈ Ioo ((τ : ℝ) - (ρ : ℝ) ^ 2) τ ×ˢ ball (c i) ρ ∧
      (s, y) ∈ Ioo ((τ : ℝ) - (ρ : ℝ) ^ 2) τ ×ˢ ball (c i) ρ ∧
      Ioo ((τ : ℝ) - 4 * (15 * r / 32) ^ 2) (τ : ℝ) ×ˢ ball (c i) (2 * (15 * r / 32)) ⊆
        Ioo (top - 4 * r ^ 2) top ×ˢ ball x₀ (2 * r) := by
  have hR : 0 < 15 * r / 32 := by positivity
  have hsmall : 16 * δ ≤ 15 * r / 32 := by linarith
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one
    (div_pos (by positivity : 0 < 16 * δ) hR)
    ((div_le_one hR).mpr hsmall)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hscale : 16 * δ ≤ (15 * r / 32) * (1 / 2 : ℝ) ^ n := by
    have h := (div_le_iff₀ hR).mp hnhi
    nlinarith
  have hscale' : (15 * r / 32) * (1 / 2 : ℝ) ^ n < 32 * δ := by
    rw [pow_succ] at hnlo
    have h := (lt_div_iff₀ hR).mp hnlo
    nlinarith
  obtain ⟨τ, ρ, i, hτlo, hτtop, _, hci, hρlo, hρhi, hpair, hpair'⟩ :=
    exists_rational_cylinder_containing_pair c hc hδ htop htime hspace hscale
  refine ⟨n, τ, ρ, i, hscale, hscale', hρlo, hρhi, hpair, hpair', ?_⟩
  exact holder_comparison_cylinder_subset hr hδr hx hci ht
    ((le_max_left t s).trans_lt hτlo) hτtop.le

end HeatKernel

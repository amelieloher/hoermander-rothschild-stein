-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HolderDyadicCylinders

/-! Quantitative pair comparison from rational-cylinder oscillation bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open Set Metric
namespace HeatKernel

/-- Rational-cylinder value bounds and dyadic oscillation control give a
quantitative modulus for nearby pairs. Radius monotonicity and the dyadic
oscillation estimate are explicit inputs. -/
theorem abs_sub_le_of_rational_cylinder_oscillation
    {α : Type*} [PseudoMetricSpace α] (c : ℕ → α) (hc : DenseRange c)
    (u : ℝ × α → ℝ) (ω : ℝ → α → ℝ → ℝ)
    {x y x₀ : α} {t s top r δ a θ W : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hδr : δ < r / 64)
    (hx : dist x x₀ < r) (ht : top - r ^ 2 < t)
    (htop : max t s < top) (htime : |t - s| ≤ δ ^ 2) (hspace : dist x y ≤ δ)
    (ha : 0 ≤ a) (hθ : 0 ≤ θ) (hθa : θ ≤ (1 / 2 : ℝ) ^ a) (hW : 0 ≤ W)
    (hpair : ∀ (τ ρ : ℚ) (i : ℕ),
      (t, x) ∈ Ioo ((τ : ℝ) - (ρ : ℝ) ^ 2) τ ×ˢ ball (c i) ρ →
      (s, y) ∈ Ioo ((τ : ℝ) - (ρ : ℝ) ^ 2) τ ×ˢ ball (c i) ρ →
      |u (t, x) - u (s, y)| ≤ ω τ (c i) ρ)
    (hmono : ∀ τ i, MonotoneOn (ω τ (c i)) (Icc 0 (15 * r / 32)))
    (hdecay : ∀ τ i,
      Ioo (τ - 4 * (15 * r / 32) ^ 2) τ ×ˢ ball (c i) (2 * (15 * r / 32)) ⊆
        Ioo (top - 4 * r ^ 2) top ×ˢ ball x₀ (2 * r) →
      ∀ n : ℕ, ω τ (c i) ((15 * r / 32) * (1 / 2 : ℝ) ^ n) ≤ θ ^ n * W) :
    |u (t, x) - u (s, y)| ≤ (1024 / 15 : ℝ) ^ a * (δ / r) ^ a * W := by
  obtain ⟨n, τ, ρ, i, hscale, hscale', hρ, hρscale, htx, hsy, hsub⟩ :=
    exists_dyadic_rational_cylinder_comparison c hc hr hδ hδr hx ht htop htime hspace
  have hR : 0 < 15 * r / 32 := by positivity
  have hscaleR : (15 * r / 32) * (1 / 2 : ℝ) ^ n ≤ 15 * r / 32 :=
    mul_le_of_le_one_right hR.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hρpos : 0 ≤ (ρ : ℝ) := by linarith
  have hbound := (hpair τ ρ i htx hsy).trans
    ((hmono τ i ⟨hρpos, hρscale.le.trans hscaleR⟩
      ⟨by positivity, hscaleR⟩ hρscale.le).trans (hdecay τ i hsub n))
  have hpow : θ ^ n ≤ ((1 / 2 : ℝ) ^ n) ^ a := by
    calc
      θ ^ n ≤ ((1 / 2 : ℝ) ^ a) ^ n := pow_le_pow_left₀ hθ hθa n
      _ = _ := by
        rw [← Real.rpow_mul_natCast (by norm_num), mul_comm a (n : ℝ),
          Real.rpow_natCast_mul (by norm_num)]
  have hnear : (1 / 2 : ℝ) ^ n ≤ (1024 / 15 : ℝ) * (δ / r) := by
    have h : (1 / 2 : ℝ) ^ n ≤ ((1024 / 15 : ℝ) * δ) / r :=
      (le_div_iff₀ hr).mpr (by nlinarith)
    convert h using 1
    ring
  calc
    _ ≤ θ ^ n * W := hbound
    _ ≤ ((1 / 2 : ℝ) ^ n) ^ a * W := mul_le_mul_of_nonneg_right hpow hW
    _ ≤ ((1024 / 15 : ℝ) * (δ / r)) ^ a * W :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (by positivity) hnear ha) hW
    _ = _ := by rw [Real.mul_rpow (by norm_num) (div_nonneg hδ.le hr.le)]

end HeatKernel

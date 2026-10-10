-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.ChainBounds
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Tactic

/-! # Kernel products restricted to chain balls

Short links remain near diagonal after integrating the intermediate points over
small balls. The finite convolution induction then yields one lower-bound factor
per link and one ball-volume factor per intermediate point.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory Metric
open scoped ENNReal
namespace HeatKernel.Gaussian

/-- A short metric chain and a near-diagonal estimate give the restricted-ball
kernel product. All convolution identities are required only at the finite
positive integer times used in this chain. -/
theorem kernel_product_lower_bound_of_short_chain {α : Type*}
    [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) (k : ℕ → α → α → ℝ≥0∞) (n : ℕ)
    (c : ℕ → α) {x y : α} (hx : c 0 = x) (hy : c (n + 1) = y)
    {r : ℝ} (hr : 0 < r) {a m : ℝ≥0∞}
    (hlinks : ∀ j, j ≤ n → dist (c j) (c (j + 1)) ≤ (3 / 16 : ℝ) * r)
    (hvol : ∀ j, j ≤ n → μ (ball (c j) (r / 32)) = m)
    (hnear : ∀ z w, dist z w ≤ r / 4 → a ≤ k 1 z w)
    (hconv : ∀ j, j < n → ∀ w, k (j + 2) x w = ∫⁻ z, k (j + 1) x z * k 1 z w ∂μ) :
    a ^ (n + 1) * m ^ n ≤ k (n + 1) x y := by
  let S := fun j : ℕ => ball (c j) (r / 32)
  have hr32 : 0 < r / 32 := by positivity
  apply kernel_chain_lower_bound_of_convolution μ k S x ?_ n (fun _ => measurableSet_ball)
    hvol ?_ hconv ?_
  · change dist x (c 0) < r / 32
    simpa only [hx, dist_self] using hr32
  · intro j hj z w hz hw
    apply hnear
    apply dist_le_quarter_of_chain_balls (hlinks j hj)
    · exact (show dist z (c j) < r / 32 from hz).le
    · exact (show dist w (c (j + 1)) < r / 32 from hw).le
  · change dist y (c (n + 1)) < r / 32
    simpa only [hy, dist_self] using hr32

/-- The preceding product bound applies to a continuous-time kernel with the
pointwise convolution law, evaluated at equal positive time increments.
The spatial radius may be chosen independently of the time increment. -/
theorem kernel_product_lower_bound_of_convolution {α : Type*}
    [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) (p : ℝ → α → α → ℝ≥0∞) (n : ℕ)
    (c : ℕ → α) {x y : α} (hx : c 0 = x) (hy : c (n + 1) = y)
    {τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r) {a m : ℝ≥0∞}
    (hlinks : ∀ j, j ≤ n → dist (c j) (c (j + 1)) ≤ (3 / 16 : ℝ) * r)
    (hvol : ∀ j, j ≤ n → μ (ball (c j) (r / 32)) = m)
    (hnear : ∀ z w, dist z w ≤ r / 4 → a ≤ p τ z w)
    (hconv : ∀ s t, 0 < s → 0 < t → ∀ z w,
      p (s + t) z w = ∫⁻ v, p s z v * p t v w ∂μ) :
    a ^ (n + 1) * m ^ n ≤ p (((n + 1 : ℕ) : ℝ) * τ) x y := by
  apply kernel_product_lower_bound_of_short_chain μ (fun j => p ((j : ℝ) * τ)) n c hx hy hr
    hlinks hvol ?_ ?_
  · simpa using hnear
  · intro j _ w
    have hp : 0 < ((j + 1 : ℕ) : ℝ) * τ := by positivity
    have H := hconv (((j + 1 : ℕ) : ℝ) * τ) τ hp hτ x w
    convert H using 1
    · congr 1
      push_cast
      ring
    · simp

/-- Restricted convolution products give a Gaussian lower bound once the chain
count, near-diagonal estimate, and intermediate ball volumes are supplied. -/
theorem gaussian_lower_bound_of_restricted_chain {α : Type*}
    [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) (p : ℝ → α → α → ℝ≥0∞) (n : ℕ)
    (centers : ℕ → α) {x y : α} (hx : centers 0 = x) (hy : centers (n + 1) = y)
    {τ r c e V W b A s : ℝ} (hτ : 0 < τ) (hr : 0 < r) (hc : 0 ≤ c)
    (he : 0 < e) (hV : 0 < V) (hW : 0 < W)
    (hb : 0 < b) (hb1 : b ≤ 1) (hbase : b ≤ c * e) (hVW : e * V ≤ W)
    (hcount : ((n + 1 : ℕ) : ℝ) ≤ 1 + A * s)
    (hlinks : ∀ j, j ≤ n → dist (centers j) (centers (j + 1)) ≤ (3 / 16 : ℝ) * r)
    (hvol : ∀ j, j ≤ n → μ (ball (centers j) (r / 32)) = ENNReal.ofReal (e * V))
    (hnear : ∀ z w, dist z w ≤ r / 4 → ENNReal.ofReal (c / V) ≤ p τ z w)
    (hconv : ∀ u v, 0 < u → 0 < v → ∀ z w,
      p (u + v) z w = ∫⁻ a, p u z a * p v a w ∂μ) :
    ENNReal.ofReal (b * Real.exp (-(A * Real.log (1 / b)) * s) / W) ≤
      p (((n + 1 : ℕ) : ℝ) * τ) x y := by
  calc
    _ ≤ ENNReal.ofReal ((c / V) ^ (n + 1) * (e * V) ^ n) :=
      ENNReal.ofReal_le_ofReal
        (gaussian_div_volume_le_chain_product n he hV hW hb hb1 hbase hVW hcount)
    _ = (ENNReal.ofReal (c / V)) ^ (n + 1) * (ENNReal.ofReal (e * V)) ^ n := by
      rw [ENNReal.ofReal_mul (pow_nonneg (div_nonneg hc hV.le) _),
        ENNReal.ofReal_pow (div_nonneg hc hV.le), ENNReal.ofReal_pow (mul_nonneg he.le hV.le)]
    _ ≤ _ := kernel_product_lower_bound_of_convolution μ p n centers hx hy hτ hr hlinks hvol hnear hconv

end HeatKernel.Gaussian

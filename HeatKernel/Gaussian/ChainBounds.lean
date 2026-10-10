-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-! # Quantitative chains for Gaussian lower bounds

A nearly shortest Lipschitz curve gives a chain with quadratically many links.
A convolution inequality and uniform lower bounds on successive sets then give
a product lower bound. The geometric and kernel assumptions are explicit.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Metric
open scoped ENNReal

namespace HeatKernel.Gaussian

/-- The positive dyadic-scale chain count has a quadratic upper bound. -/
theorem max_one_ceil_le {s : ℝ} (hs : 0 ≤ s) :
    ((max 1 ⌈s⌉₊ : ℕ) : ℝ) ≤ 1 + s := by
  rw [Nat.cast_max]
  apply max_le
  · simp only [Nat.cast_one]; linarith
  · have := Nat.ceil_lt_add_one hs
    linarith

/-- The same chain count is positive and dominates its real argument. -/
theorem max_one_ceil_bounds (s : ℝ) :
    1 ≤ max 1 ⌈s⌉₊ ∧ s ≤ ((max 1 ⌈s⌉₊ : ℕ) : ℝ) := by
  constructor
  · exact le_max_left _ _
  · exact (Nat.le_ceil s).trans (by exact_mod_cast le_max_right 1 ⌈s⌉₊)

/-- The quadratic count makes each equal subdivision short on its heat scale. -/
theorem chain_step_le_sqrt {D t : ℝ} {n : ℕ} (ht : 0 < t)
    (hn : 0 < n) (hcount : 64 * D ^ 2 / t ≤ (n : ℝ)) :
    3 * D / (2 * n) ≤ (3 / 16 : ℝ) * Real.sqrt (t / n) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have htn : 0 ≤ t / (n : ℝ) := div_nonneg ht.le hnR.le
  have hs := Real.sq_sqrt htn
  have hc : 64 * D ^ 2 ≤ (n : ℝ) * t := (div_le_iff₀ ht).mp hcount
  have hsq : (8 * D / (n : ℝ)) ^ 2 ≤ (Real.sqrt (t / n)) ^ 2 := by
    rw [hs]
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hnR) hnR).mpr
    nlinarith [mul_nonneg hnR.le (sub_nonneg.mpr hc)]
  have hsmall : 8 * D / (n : ℝ) ≤ Real.sqrt (t / n) := by
    nlinarith [Real.sqrt_nonneg (t / n)]
  calc
    3 * D / (2 * n) = (3 / 16 : ℝ) * (8 * D / n) := by ring
    _ ≤ (3 / 16 : ℝ) * Real.sqrt (t / n) := mul_le_mul_of_nonneg_left hsmall (by norm_num)

/-- Perturbing adjacent chain centers within small balls preserves the near-diagonal radius. -/
theorem dist_le_quarter_of_chain_balls {α : Type*} [PseudoMetricSpace α]
    {c d z w : α} {r : ℝ} (hchain : dist c d ≤ (3 / 16 : ℝ) * r)
    (hz : dist z c ≤ r / 32) (hw : dist w d ≤ r / 32) :
    dist z w ≤ r / 4 := by
  have htri := dist_triangle4 z c d w
  rw [dist_comm d w] at htri
  linarith

/-- Uniform lower bounds along sets propagate through a convolution kernel.
The set measures supply the volume factors in the finite chain product. -/
theorem kernel_chain_lower_bound_of_convolution {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (k : ℕ → α → α → ℝ≥0∞) (S : ℕ → Set α)
    (x : α) (hx : x ∈ S 0) {a m : ℝ≥0∞} (n : ℕ)
    (hS : ∀ j, MeasurableSet (S j)) (hvol : ∀ j, j ≤ n → μ (S j) = m)
    (hstep : ∀ j, j ≤ n → ∀ z w, z ∈ S j → w ∈ S (j + 1) → a ≤ k 1 z w)
    (hconv : ∀ j, j < n → ∀ y, k (j + 2) x y = ∫⁻ z, k (j + 1) x z * k 1 z y ∂μ)
    {y : α} (hy : y ∈ S (n + 1)) :
    a ^ (n + 1) * m ^ n ≤ k (n + 1) x y := by
  have haux : ∀ j, j ≤ n → ∀ y ∈ S (j + 1),
      a ^ (j + 1) * m ^ j ≤ k (j + 1) x y := by
    intro j
    induction j with
    | zero =>
      intro _ y hy
      simpa using hstep 0 (Nat.zero_le n) x y hx hy
    | succ j ih =>
      intro hj y hy
      rw [hconv j (by omega) y]
      calc
        a ^ (j + 1 + 1) * m ^ (j + 1) =
            (a ^ (j + 1) * m ^ j * a) * μ (S (j + 1)) := by
          simp only [hvol (j + 1) hj, pow_succ]
          ac_rfl
        _ = ∫⁻ z in S (j + 1), a ^ (j + 1) * m ^ j * a ∂μ :=
          (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ z in S (j + 1), k (j + 1) x z * k 1 z y ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem (hS (j + 1))] with z hz
          exact mul_le_mul' (ih (by omega) z hz) (hstep (j + 1) hj z y hz hy)
        _ ≤ ∫⁻ z, k (j + 1) x z * k 1 z y ∂μ :=
          lintegral_mono' Measure.restrict_le_self le_rfl
  exact haux n le_rfl y hy

/-- A product with quadratically many factors has a Gaussian lower bound. -/
theorem gaussian_le_pow_of_chain_count {b A s : ℝ} {n : ℕ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hcount : (n : ℝ) ≤ 1 + A * s) :
    b * Real.exp (-(A * Real.log (1 / b)) * s) ≤ b ^ n := by
  rw [← Real.rpow_natCast]
  calc
    b * Real.exp (-(A * Real.log (1 / b)) * s) = b ^ (1 + A * s) := by
      rw [Real.rpow_add hb, Real.rpow_one, Real.rpow_def_of_pos hb, Real.log_div (by norm_num) hb.ne',
        Real.log_one]
      congr 2
      ring
    _ ≤ b ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_ge hb hb1 hcount

/-- Cancellation of the intermediate volumes in a finite chain product. -/
theorem chain_product_eq {c e V : ℝ} (he : e ≠ 0) (hV : V ≠ 0) (n : ℕ) :
    (c / V) ^ (n + 1) * (e * V) ^ n = (c * e) ^ (n + 1) / (e * V) := by
  rw [div_pow, mul_pow, mul_pow, pow_succ e, pow_succ V]
  field_simp

/-- A volume-scaled chain product dominates a Gaussian when the number of links
is quadratic in distance. The intermediate volume comparison is explicit. -/
theorem gaussian_div_volume_le_chain_product {c e V W b A s : ℝ} (n : ℕ)
    (he : 0 < e) (hV : 0 < V) (hW : 0 < W)
    (hb : 0 < b) (hb1 : b ≤ 1) (hbase : b ≤ c * e)
    (hvol : e * V ≤ W) (hcount : ((n + 1 : ℕ) : ℝ) ≤ 1 + A * s) :
    b * Real.exp (-(A * Real.log (1 / b)) * s) / W ≤
      (c / V) ^ (n + 1) * (e * V) ^ n := by
  rw [chain_product_eq he.ne' hV.ne']
  calc
    _ ≤ b ^ (n + 1) / W :=
      div_le_div_of_nonneg_right (gaussian_le_pow_of_chain_count hb hb1 hcount) hW.le
    _ ≤ (c * e) ^ (n + 1) / W :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hb.le hbase _) hW.le
    _ ≤ (c * e) ^ (n + 1) / (e * V) :=
      div_le_div_of_nonneg_left (pow_nonneg (hb.le.trans hbase) _) (mul_pos he hV) hvol

end HeatKernel.Gaussian

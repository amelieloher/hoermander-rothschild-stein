-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.SobolevScale
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

noncomputable section

open LineDeriv MeasureTheory SchwartzMap
open scoped BigOperators FourierTransform

namespace Hormander.C

/-- The squared inhomogeneous Fourier Sobolev quantity for a Schwartz function. -/
def weightedFourierSq {N : ℕ} (s : ℝ) (u : 𝓢(Hormander.A.Carrier N, ℂ)) : ℝ :=
  ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 u ξ‖ ^ 2

/-- The squared L² quantity for a Schwartz function. -/
def functionL2Sq {N : ℕ} (u : 𝓢(Hormander.A.Carrier N, ℂ)) : ℝ :=
  ∫ x, ‖u x‖ ^ 2

/-- Schwartz functions have an integrable squared norm. -/
theorem schwartz_norm_sq_integrable {N : ℕ} (f : 𝓢(Hormander.A.Carrier N, ℂ)) :
    Integrable (fun x => ‖f x‖ ^ 2) := by
  let c : ℝ := SchwartzMap.seminorm ℂ 0 0 f
  have hc : 0 ≤ c := by
    have h0 : ‖f 0‖ ≤ c := by
      simpa [c] using (SchwartzMap.le_seminorm ℂ 0 0 f (0 : Hormander.A.Carrier N))
    exact (norm_nonneg (f 0)).trans h0
  have hbound (x : Hormander.A.Carrier N) : ‖f x‖ ≤ c := by
    simpa [c] using (SchwartzMap.le_seminorm ℂ 0 0 f x)
  have h0 : Integrable (fun x : Hormander.A.Carrier N => ‖f x‖) := by
    simpa using f.integrable_pow_mul volume 0
  have h2 : Integrable (fun x : Hormander.A.Carrier N => ‖x‖ ^ 2 * ‖f x‖) :=
    f.integrable_pow_mul volume 2
  have hbase : Integrable (fun x : Hormander.A.Carrier N => (1 + ‖x‖ ^ 2) * ‖f x‖) := by
    have hEq : (fun x : Hormander.A.Carrier N => (1 + ‖x‖ ^ 2) * ‖f x‖) =
        (fun x => ‖f x‖) + (fun x => ‖x‖ ^ 2 * ‖f x‖) := by
      funext x
      change (1 + ‖x‖ ^ 2) * ‖f x‖ = ‖f x‖ + ‖x‖ ^ 2 * ‖f x‖
      ring
    rw [hEq]
    exact h0.add h2
  refine (hbase.mul_const c).mono' (by fun_prop) ?_
  filter_upwards with x
  have hnorm : 0 ≤ ‖f x‖ := norm_nonneg _
  have hdom : ‖f x‖ ^ 2 ≤ c * ‖f x‖ := by
    nlinarith [hbound x]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  calc
    ‖f x‖ ^ 2 ≤ c * ‖f x‖ := hdom
    _ ≤ ((1 + ‖x‖ ^ 2) * ‖f x‖) * c := by
      have hx : 1 ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
      calc
        c * ‖f x‖ = 1 * (‖f x‖ * c) := by ring
        _ ≤ (1 + ‖x‖ ^ 2) * (‖f x‖ * c) :=
          mul_le_mul_of_nonneg_right hx (mul_nonneg hnorm hc)
        _ = ((1 + ‖x‖ ^ 2) * ‖f x‖) * c := by ring

/-- A real power of order at most one grows no faster than the quadratic weight. -/
theorem weightedFourierSq_integrable {N : ℕ} {s : ℝ} (hs : s ≤ 1)
    (u : 𝓢(Hormander.A.Carrier N, ℂ)) :
    Integrable (fun ξ => (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 u ξ‖ ^ 2) := by
  let f : 𝓢(Hormander.A.Carrier N, ℂ) := 𝓕 u
  let c : ℝ := SchwartzMap.seminorm ℂ 0 0 f
  have hc : 0 ≤ c := by
    have h0 : ‖f 0‖ ≤ c := by
      simpa [c] using (SchwartzMap.le_seminorm ℂ 0 0 f (0 : Hormander.A.Carrier N))
    exact (norm_nonneg (f 0)).trans h0
  have hbound (x : Hormander.A.Carrier N) : ‖f x‖ ≤ c := by
    simpa [c] using (SchwartzMap.le_seminorm ℂ 0 0 f x)
  have h0 : Integrable (fun x : Hormander.A.Carrier N => ‖f x‖) := by
    simpa using f.integrable_pow_mul volume 0
  have h2 : Integrable (fun x : Hormander.A.Carrier N => ‖x‖ ^ 2 * ‖f x‖) :=
    f.integrable_pow_mul volume 2
  have hbase : Integrable (fun x : Hormander.A.Carrier N => (1 + ‖x‖ ^ 2) * ‖f x‖) := by
    have hEq : (fun x : Hormander.A.Carrier N => (1 + ‖x‖ ^ 2) * ‖f x‖) =
        (fun x => ‖f x‖) + (fun x => ‖x‖ ^ 2 * ‖f x‖) := by
      funext x
      change (1 + ‖x‖ ^ 2) * ‖f x‖ = ‖f x‖ + ‖x‖ ^ 2 * ‖f x‖
      ring
    rw [hEq]
    exact h0.add h2
  have hweightCont : Continuous (fun x : Hormander.A.Carrier N =>
      (1 + ‖x‖ ^ 2) ^ s) :=
    Continuous.rpow_const (by fun_prop) (fun x => Or.inl (by positivity))
  have hFourierNormCont : Continuous (fun x : Hormander.A.Carrier N => ‖f x‖ ^ 2) := by
    fun_prop
  refine (hbase.mul_const c).mono' (hweightCont.mul hFourierNormCont).aestronglyMeasurable ?_
  filter_upwards with x
  let b : ℝ := 1 + ‖x‖ ^ 2
  have hb : 1 ≤ b := by dsimp [b]; nlinarith [sq_nonneg ‖x‖]
  have hpow : b ^ s ≤ b := by
    calc
      b ^ s ≤ b ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb hs
      _ = b := Real.rpow_one b
  have hwt : 0 ≤ b ^ s := Real.rpow_nonneg (by positivity) _
  have hnorm : 0 ≤ ‖f x‖ := norm_nonneg _
  have hsq : ‖f x‖ ^ 2 ≤ c * ‖f x‖ := by nlinarith [hbound x]
  have hdom : b ^ s * ‖f x‖ ^ 2 ≤ (b * ‖f x‖) * c := by
    calc
      b ^ s * ‖f x‖ ^ 2 ≤ b * ‖f x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
      _ ≤ b * (c * ‖f x‖) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (b * ‖f x‖) * c := by ring
  have hnonneg : 0 ≤ b ^ s * ‖f x‖ ^ 2 := mul_nonneg hwt (sq_nonneg _)
  rw [Real.norm_of_nonneg hnonneg]
  simpa [b] using hdom

/-- The frequency weight splits into its zero-order and coordinate-derivative parts. -/
theorem inhomogeneous_weight_le_coordinate {N : ℕ} {δ : ℝ} (hδ : δ < 1)
    (ξ : Hormander.A.Carrier N) :
    (1 + ‖ξ‖ ^ 2) ^ δ ≤
      1 + ‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (δ - 1) := by
  let b : ℝ := 1 + ‖ξ‖ ^ 2
  have hb : 1 ≤ b := by dsimp [b]; nlinarith [sq_nonneg ‖ξ‖]
  have hneg : b ^ (δ - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hb (by linarith)
  have hsplit : b ^ δ = b ^ (δ - 1) * b := by
    calc
      b ^ δ = b ^ ((δ - 1) + 1) := by congr 1; ring
      _ = b ^ (δ - 1) * b ^ (1 : ℝ) := Real.rpow_add (by positivity) _ _
      _ = b ^ (δ - 1) * b := by rw [Real.rpow_one]
  rw [show (1 + ‖ξ‖ ^ 2) ^ δ = b ^ δ by rfl, hsplit]
  calc
    b ^ (δ - 1) * b = b ^ (δ - 1) + ‖ξ‖ ^ 2 * b ^ (δ - 1) := by
      dsimp [b]
      ring
    _ ≤ 1 + ‖ξ‖ ^ 2 * b ^ (δ - 1) := by nlinarith [hneg]

/-- The Fourier transform of a line derivative has the expected coordinate multiplier in
absolute value. -/
theorem fourier_lineDeriv_norm_sq {N : ℕ} (u : 𝓢(Hormander.A.Carrier N, ℂ))
    (v ξ : Hormander.A.Carrier N) :
    ‖𝓕 (∂_{v} u) ξ‖ ^ 2 =
      (2 * Real.pi) ^ 2 * ‖inner ℝ ξ v‖ ^ 2 * ‖𝓕 u ξ‖ ^ 2 := by
  have hgrowth : (inner ℝ · v).HasTemperateGrowth :=
    ((innerSL ℝ).flip v).hasTemperateGrowth
  rw [Hormander.A.fourier_schwartz_lineDeriv]
  change ‖(2 * Real.pi * Complex.I) •
      ((SchwartzMap.smulLeftCLM ℂ (inner ℝ · v) (𝓕 u)) ξ)‖ ^ 2 = _
  rw [SchwartzMap.smulLeftCLM_apply_apply hgrowth]
  simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  ring

/-- The Bessel symbol converts multiplication into the squared Sobolev weight. -/
theorem besselSymbol_mul_norm_sq {N : ℕ} (s : ℝ) (ξ : Hormander.A.Carrier N)
    (z : ℂ) :
    ‖(Hormander.A.besselSymbol s ξ) * z‖ ^ 2 =
      (1 + ‖ξ‖ ^ 2) ^ s * ‖z‖ ^ 2 := by
  change ‖Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ (s / 2)) * z‖ ^ 2 = _
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hb : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt hb) _), mul_pow,
    ← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (s / 2)) 2,
    ← Real.rpow_mul (le_of_lt hb)]
  congr 1
  ring_nf

/-- Fourier transformation turns the weighted integral into the L² norm of the Bessel
multiplier. -/
theorem weightedFourierSq_eq_Lambda_integral {N : ℕ} (s : ℝ)
    (u : 𝓢(Hormander.A.Carrier N, ℂ)) :
    weightedFourierSq s u = ∫ x, ‖Hormander.A.Lambda s u x‖ ^ 2 := by
  calc
    weightedFourierSq s u =
        ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 u ξ‖ ^ 2 := rfl
    _ = ∫ ξ, ‖𝓕 (Hormander.A.Lambda s u) ξ‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [Hormander.A.fourier_Lambda,
        SchwartzMap.smulLeftCLM_apply_apply
          (Hormander.A.besselSymbol_hasTemperateGrowth s)]
      exact (besselSymbol_mul_norm_sq s ξ (𝓕 u ξ)).symm
    _ = ∫ x, ‖Hormander.A.Lambda s u x‖ ^ 2 :=
      SchwartzMap.integral_norm_sq_fourier (Hormander.A.Lambda s u)

/-- The squared L² norm of a Schwartz function is its squared Bochner L² norm. -/
theorem functionL2Sq_eq_toLp_norm_sq {N : ℕ} (f : 𝓢(Hormander.A.Carrier N, ℂ)) :
    functionL2Sq f = ‖f.toLp 2‖ ^ 2 := by
  unfold functionL2Sq
  rw [SchwartzMap.norm_toLp' (p := 2) (by norm_num) (by norm_num)]
  norm_num
  rw [← Real.sqrt_eq_rpow]
  exact (Real.sq_sqrt (integral_nonneg fun x => sq_nonneg ‖f x‖)).symm

/-- The weighted Fourier integral is the squared norm in the selected Bessel-potential scale. -/
theorem weightedFourierSq_eq_schwartzSobolevNorm_sq {N : ℕ} (s : ℝ)
    (u : 𝓢(Hormander.A.Carrier N, ℂ)) :
    weightedFourierSq s u = Hormander.A.schwartzSobolevNorm s u ^ 2 := by
  unfold Hormander.A.schwartzSobolevNorm
  rw [weightedFourierSq_eq_Lambda_integral]
  exact (functionL2Sq_eq_toLp_norm_sq (Hormander.A.Lambda s u))

/-- The coordinate estimate in its weighted Fourier integral form. -/
theorem fourier_coordinate_estimate_integral {N : ℕ} {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (u : 𝓢(Hormander.A.Carrier N, ℂ)) :
    weightedFourierSq δ u ≤ functionL2Sq u + ((2 * Real.pi) ^ 2)⁻¹ *
      ∑ i : Fin N, weightedFourierSq (δ - 1)
        (∂_{EuclideanSpace.single i (1 : ℝ)} u) := by
  let a : ℝ := (2 * Real.pi) ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hcoord (ξ : Hormander.A.Carrier N) :
      ∑ i : Fin N, ‖inner ℝ ξ (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 = ‖ξ‖ ^ 2 := by
    calc
      ∑ i : Fin N, ‖inner ℝ ξ (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 =
          ∑ i : Fin N, (ξ i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [EuclideanSpace.inner_single_right]
            simp
      _ = ‖ξ‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq ξ).symm
  have hsum (ξ : Hormander.A.Carrier N) :
      ∑ i : Fin N, (1 + ‖ξ‖ ^ 2) ^ (δ - 1) *
          ‖𝓕 (∂_{EuclideanSpace.single i (1 : ℝ)} u) ξ‖ ^ 2 =
        a * (1 + ‖ξ‖ ^ 2) ^ (δ - 1) * ‖𝓕 u ξ‖ ^ 2 * ‖ξ‖ ^ 2 := by
    calc
      _ = ∑ i : Fin N, (a * (1 + ‖ξ‖ ^ 2) ^ (δ - 1) * ‖𝓕 u ξ‖ ^ 2) *
          ‖inner ℝ ξ (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [fourier_lineDeriv_norm_sq]
          ring
      _ = a * (1 + ‖ξ‖ ^ 2) ^ (δ - 1) * ‖𝓕 u ξ‖ ^ 2 *
          ∑ i : Fin N, ‖inner ℝ ξ (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
          rw [← Finset.mul_sum]
      _ = _ := by rw [hcoord]
  have hpoint (ξ : Hormander.A.Carrier N) :
      (1 + ‖ξ‖ ^ 2) ^ δ * ‖𝓕 u ξ‖ ^ 2 ≤
        ‖𝓕 u ξ‖ ^ 2 + a⁻¹ * ∑ i : Fin N, (1 + ‖ξ‖ ^ 2) ^ (δ - 1) *
          ‖𝓕 (∂_{EuclideanSpace.single i (1 : ℝ)} u) ξ‖ ^ 2 := by
    rw [hsum]
    have hw := inhomogeneous_weight_le_coordinate hδ1 ξ
    have hcancel : a⁻¹ * (a * (1 + ‖ξ‖ ^ 2) ^ (δ - 1) *
        ‖𝓕 u ξ‖ ^ 2 * ‖ξ‖ ^ 2) =
        ‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (δ - 1) * ‖𝓕 u ξ‖ ^ 2 := by
      field_simp [ha.ne']
    rw [hcancel]
    calc
      (1 + ‖ξ‖ ^ 2) ^ δ * ‖𝓕 u ξ‖ ^ 2 ≤
          (1 + ‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (δ - 1)) * ‖𝓕 u ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
      _ = ‖𝓕 u ξ‖ ^ 2 +
          ‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (δ - 1) * ‖𝓕 u ξ‖ ^ 2 := by ring
  have hδm1 : δ - 1 ≤ 1 := by linarith
  have hleft : Integrable (fun ξ : Hormander.A.Carrier N =>
      (1 + ‖ξ‖ ^ 2) ^ δ * ‖𝓕 u ξ‖ ^ 2) := weightedFourierSq_integrable (by linarith) u
  have hbase : Integrable (fun ξ : Hormander.A.Carrier N => ‖𝓕 u ξ‖ ^ 2) :=
    schwartz_norm_sq_integrable (𝓕 u)
  have hsumInt : Integrable (fun ξ : Hormander.A.Carrier N =>
      ∑ i : Fin N, (1 + ‖ξ‖ ^ 2) ^ (δ - 1) *
        ‖𝓕 (∂_{EuclideanSpace.single i (1 : ℝ)} u) ξ‖ ^ 2) := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    exact weightedFourierSq_integrable hδm1
      (∂_{EuclideanSpace.single i (1 : ℝ)} u)
  have hscaled : Integrable (fun ξ : Hormander.A.Carrier N => a⁻¹ *
      ∑ i : Fin N, (1 + ‖ξ‖ ^ 2) ^ (δ - 1) *
        ‖𝓕 (∂_{EuclideanSpace.single i (1 : ℝ)} u) ξ‖ ^ 2) := by
    simpa [mul_comm] using hsumInt.mul_const a⁻¹
  have hright : Integrable (fun ξ : Hormander.A.Carrier N =>
      ‖𝓕 u ξ‖ ^ 2 + a⁻¹ * ∑ i : Fin N, (1 + ‖ξ‖ ^ 2) ^ (δ - 1) *
        ‖𝓕 (∂_{EuclideanSpace.single i (1 : ℝ)} u) ξ‖ ^ 2) :=
    hbase.add hscaled
  calc
    weightedFourierSq δ u =
        ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ δ * ‖𝓕 u ξ‖ ^ 2 := rfl
    _ ≤ ∫ ξ, ‖𝓕 u ξ‖ ^ 2 + a⁻¹ * ∑ i : Fin N, (1 + ‖ξ‖ ^ 2) ^ (δ - 1) *
          ‖𝓕 (∂_{EuclideanSpace.single i (1 : ℝ)} u) ξ‖ ^ 2 :=
      integral_mono hleft hright (by intro ξ; exact hpoint ξ)
    _ = functionL2Sq u + a⁻¹ * ∑ i : Fin N, weightedFourierSq (δ - 1)
          (∂_{EuclideanSpace.single i (1 : ℝ)} u) := by
      rw [integral_add hbase hscaled, integral_const_mul a⁻¹,
        SchwartzMap.integral_norm_sq_fourier u]
      rw [integral_finsetSum Finset.univ (by
        intro i hi
        exact weightedFourierSq_integrable hδm1
          (∂_{EuclideanSpace.single i (1 : ℝ)} u))]
      simp [functionL2Sq, weightedFourierSq]

end Hormander.C

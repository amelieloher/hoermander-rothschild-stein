-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Energy.Pairing

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped ComplexConjugate

namespace Hormander.C

open Hormander.B

variable {N : ℕ}

theorem energy_identity (X : RealSchwartzVectorField N) (φ : TestFunction N) :
    normSq (vectorFieldOperator X φ) =
      -(hermitianPairing (vectorFieldOperator X (vectorFieldOperator X φ)) φ).re +
        (hermitianPairing (realMultiplierOperator (negDiv X) (vectorFieldOperator X φ)) φ).re := by
  have h := vectorField_hasHermitianAdjoint X φ (vectorFieldOperator X φ)
  rw [H_self] at h
  simp only [LinearMap.add_apply, LinearMap.neg_apply] at h
  rw [H_add_right, H_neg_right] at h
  have := congrArg Complex.re h
  simp only [Complex.ofReal_re, Complex.add_re, Complex.neg_re] at this
  rw [H_re_symm φ, H_re_symm φ] at this
  exact this

/-- Drift identity `2 Re (X φ, φ) = ((-div X)φ, φ)`. -/
theorem drift_identity (X : RealSchwartzVectorField N) (φ : TestFunction N) :
    2 * (hermitianPairing (vectorFieldOperator X φ) φ).re =
      ∫ x, negDiv X x * ‖φ x‖ ^ 2 := by
  have h := vectorField_hasHermitianAdjoint X φ φ
  simp only [LinearMap.add_apply, LinearMap.neg_apply] at h
  rw [H_add_right, H_neg_right] at h
  have := congrArg Complex.re h
  simp only [Complex.add_re, Complex.neg_re] at this
  rw [H_re_symm φ (vectorFieldOperator X φ), H_re_symm φ (realMultiplierOperator (negDiv X) φ),
    H_realMultiplier] at this
  linarith


/-- Young step: a bounded multiplier energy. -/
theorem integral_mult_le (g : SchwartzMap (Carrier N) ℝ) (G : ℝ) (hG : ∀ x, |g x| ≤ G)
    (φ : TestFunction N) : ∫ x, g x * ‖φ x‖ ^ 2 ≤ G * normSq φ := by
  have hint : Integrable (fun x => g x * ‖φ x‖ ^ 2) volume := by
    refine Integrable.mono' ((integrable_sqnorm φ).const_mul G)
      (g.continuous.mul (φ.continuous.norm.pow 2)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖φ x‖ ^ 2)]
    exact mul_le_mul_of_nonneg_right (hG x) (by positivity)
  unfold normSq
  rw [← integral_const_mul]
  refine integral_mono hint ((integrable_sqnorm φ).const_mul G) fun x => ?_
  exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hG x)) (by positivity)

/-- Young absorption for the pairing
`|(g w, φ)| ≤ ½‖w‖² + ½ G²‖φ‖²`. -/
theorem re_H_mult_le (g : SchwartzMap (Carrier N) ℝ) (G : ℝ) (hG : ∀ x, |g x| ≤ G)
    (w φ : TestFunction N) :
    (hermitianPairing (realMultiplierOperator g w) φ).re ≤
      (1 / 2) * normSq w + (1 / 2) * G ^ 2 * normSq φ := by
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG 0)
  refine (Complex.re_le_norm _).trans ?_
  unfold hermitianPairing
  refine (norm_integral_le_integral_norm _).trans ?_
  have hint := (integrable_pair (realMultiplierOperator g w) φ).norm
  have hrhs : Integrable (fun x => (1 / 2) * ‖w x‖ ^ 2 + (1 / 2) * G ^ 2 * ‖φ x‖ ^ 2) volume :=
    ((integrable_sqnorm w).const_mul (1 / 2)).add ((integrable_sqnorm φ).const_mul ((1 / 2) * G ^ 2))
  have : (1 / 2) * normSq w + (1 / 2) * G ^ 2 * normSq φ =
      ∫ x, ((1 / 2) * ‖w x‖ ^ 2 + (1 / 2) * G ^ 2 * ‖φ x‖ ^ 2) := by
    unfold normSq
    rw [integral_add ((integrable_sqnorm w).const_mul (1 / 2))
      ((integrable_sqnorm φ).const_mul ((1 / 2) * G ^ 2)), integral_const_mul, integral_const_mul]
  rw [this]
  refine integral_mono hint hrhs fun x => ?_
  have e : realMultiplierOperator g w x = (g x : ℂ) * w x := by
    unfold realMultiplierOperator
    rw [multiplierOperator_apply, complexifyRealSchwartz_apply]
  rw [e, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
  have h1 : |g x| * ‖w x‖ * ‖φ x‖ ≤ G * ‖w x‖ * ‖φ x‖ := by
    gcongr; exact hG x
  nlinarith [sq_nonneg (‖w x‖ - G * ‖φ x‖), norm_nonneg (w x), norm_nonneg (φ x)]


/-- The operator `L = ∑_{j=1}^k X_j² + X_0 + c`. -/
def diffusionOperator {k : ℕ} (X : Fin (k + 1) → RealSchwartzVectorField N)
    (c : SchwartzMap (Carrier N) ℝ) : Operator N :=
  (∑ i : Fin k, (vectorFieldOperator (X i.succ)).comp (vectorFieldOperator (X i.succ))) +
    vectorFieldOperator (X 0) + realMultiplierOperator c

/-- Complex energy estimate (BB Lemma 5.51): `∑_{j=1}^k ‖X_j φ‖₂² ≤ C (|(Lφ,φ)| + ‖φ‖₂²)`
for every complex Schwartz `φ`, with `C = max 2 (G₀ + 2 C_c + ∑_{j≥1} G_j²)` depending only on `k`
and the bounds `|g_j| ≤ G_j` (`g_j = -div X_j`), `|c| ≤ C_c`. -/
theorem complex_energy_estimate {k : ℕ} (X : Fin (k + 1) → RealSchwartzVectorField N)
    (c : SchwartzMap (Carrier N) ℝ) (G : Fin (k + 1) → ℝ) (Cc : ℝ)
    (hG : ∀ j x, |negDiv (X j) x| ≤ G j) (hc : ∀ x, |c x| ≤ Cc) (φ : TestFunction N) :
    ∑ j : Fin k, normSq (vectorFieldOperator (X j.succ) φ) ≤
      max 2 (G 0 + 2 * Cc + ∑ j : Fin k, G j.succ ^ 2) *
        (‖hermitianPairing (diffusionOperator X c φ) φ‖ + normSq φ) := by
  set n := normSq φ with hn
  have hn0 : 0 ≤ n := normSq_nonneg φ
  have hCc0 : 0 ≤ Cc := (abs_nonneg _).trans (hc 0)
  have hG0 : ∀ j, 0 ≤ G j := fun j => (abs_nonneg _).trans (hG j 0)
  set S : TestFunction N := ∑ i : Fin k, vectorFieldOperator (X i.succ) (vectorFieldOperator (X i.succ) φ) with hS
  have hL : diffusionOperator X c φ = S + vectorFieldOperator (X 0) φ + realMultiplierOperator c φ := by
    unfold diffusionOperator
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    rfl
  have hHL : hermitianPairing (diffusionOperator X c φ) φ =
      hermitianPairing S φ + hermitianPairing (vectorFieldOperator (X 0) φ) φ +
        hermitianPairing (realMultiplierOperator c φ) φ := by
    rw [hL, H_add_left, H_add_left]
  have hHS : (hermitianPairing S φ).re =
      ∑ i : Fin k, (hermitianPairing (vectorFieldOperator (X i.succ) (vectorFieldOperator (X i.succ) φ)) φ).re := by
    rw [hS, H_sum_left, Complex.re_sum]
  -- per-field inequality
  have hj : ∀ i : Fin k, normSq (vectorFieldOperator (X i.succ) φ) ≤
      -(hermitianPairing (vectorFieldOperator (X i.succ) (vectorFieldOperator (X i.succ) φ)) φ).re +
        ((1 / 2) * normSq (vectorFieldOperator (X i.succ) φ) + (1 / 2) * G i.succ ^ 2 * n) := by
    intro i
    have e := energy_identity (X i.succ) φ
    have := re_H_mult_le (negDiv (X i.succ)) (G i.succ) (hG i.succ) (vectorFieldOperator (X i.succ) φ) φ
    linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hj i)
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, ← hHS] at hsum
  -- drift and zeroth order
  have hdrift : (hermitianPairing (vectorFieldOperator (X 0) φ) φ).re ≤ (1 / 2) * G 0 * n := by
    have h1 := drift_identity (X 0) φ
    have h2 := integral_mult_le (negDiv (X 0)) (G 0) (hG 0) φ
    linarith
  have hzero : (hermitianPairing (realMultiplierOperator c φ) φ).re ≤ Cc * n := by
    rw [H_realMultiplier]; exact integral_mult_le c Cc hc φ
  have hre : -(hermitianPairing S φ).re ≤ ‖hermitianPairing (diffusionOperator X c φ) φ‖ +
      (hermitianPairing (vectorFieldOperator (X 0) φ) φ).re + (hermitianPairing (realMultiplierOperator c φ) φ).re := by
    have h1 := Complex.abs_re_le_norm (hermitianPairing (diffusionOperator X c φ) φ)
    have h2 := neg_abs_le (hermitianPairing (diffusionOperator X c φ) φ).re
    have h3 : (hermitianPairing (diffusionOperator X c φ) φ).re = (hermitianPairing S φ).re +
        (hermitianPairing (vectorFieldOperator (X 0) φ) φ).re + (hermitianPairing (realMultiplierOperator c φ) φ).re := by
      rw [hHL]; simp only [Complex.add_re]
    linarith
  set A := ∑ i : Fin k, normSq (vectorFieldOperator (X i.succ) φ) with hA
  set Q := ∑ i : Fin k, G i.succ ^ 2 with hQ
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => normSq_nonneg _
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hmain : A ≤ 2 * ‖hermitianPairing (diffusionOperator X c φ) φ‖ +
      (G 0 + 2 * Cc + Q) * n := by
    nlinarith [hsum, hre, hdrift, hzero]
  have hM1 : (2 : ℝ) ≤ max 2 (G 0 + 2 * Cc + Q) := le_max_left _ _
  have hM2 : G 0 + 2 * Cc + Q ≤ max 2 (G 0 + 2 * Cc + Q) := le_max_right _ _
  have hnorm := norm_nonneg (hermitianPairing (diffusionOperator X c φ) φ)
  nlinarith [mul_le_mul_of_nonneg_right hM1 hnorm, mul_le_mul_of_nonneg_right hM2 hn0]

end Hormander.C

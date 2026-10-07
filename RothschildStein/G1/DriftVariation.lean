-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlledVariation
public import RothschildStein.Definitions.driftWeight
public import RothschildStein.Definitions.noDriftWeight

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G1

/-- The weighted integral bound has the exact horizontal √q
and drift-square factors (BB Thm 1.56, p. 37). -/
theorem controlledCurve_drift_variation_le {q n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ 1 f Ω)
    {δ H D : ℝ} {γ : ℝ → (Fin n → ℝ)}
    (hγ : isControlledCurve Ω driftWeight X δ γ)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1,
      Real.sqrt (∑ i : Fin q, (fderiv ℝ f (γ t) (X i.succ (γ t))) ^ 2) ≤ H)
    (hD : ∀ t ∈ Icc (0 : ℝ) 1, |fderiv ℝ f (γ t) (X 0 (γ t))| ≤ D) :
    |f (γ 1) - f (γ 0)| ≤ Real.sqrt q * δ * H + δ ^ 2 * D := by
  apply controlledCurve_variation_le hΩ hf hγ
  intro t ht
  rw [Fin.sum_univ_succ]
  simp only [driftWeight, eq_self, ite_true, show ((2 : ℕ+) : ℕ) = 2 from rfl,
    Fin.succ_ne_zero, ite_false, show ((1 : ℕ+) : ℕ) = 1 from rfl, pow_one]
  have hs := (horizontal_abs_sum_le (fun i : Fin q =>
    fderiv ℝ f (γ t) (X i.succ (γ t)))).trans
      (mul_le_mul_of_nonneg_left (hH t ht) (Real.sqrt_nonneg _))
  rw [← Finset.mul_sum]
  have hm := mul_le_mul_of_nonneg_left hs hγ.1.le
  have hd := mul_le_mul_of_nonneg_left (hD t ht) (sq_nonneg δ)
  nlinarith

/-- The drift-free variation bound uses the fixed weight-one
system (BB Thm 1.54, pp. 36–37). -/
theorem controlledCurve_noDrift_variation_le {q n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ 1 f Ω)
    {δ H : ℝ} {γ : ℝ → (Fin n → ℝ)}
    (hγ : isControlledCurve Ω noDriftWeight X δ γ)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1,
      Real.sqrt (∑ i, (fderiv ℝ f (γ t) (X i (γ t))) ^ 2) ≤ H) :
    |f (γ 1) - f (γ 0)| ≤ Real.sqrt q * δ * H := by
  apply controlledCurve_variation_le hΩ hf hγ
  intro t ht
  simp only [noDriftWeight, show ((1 : ℕ+) : ℕ) = 1 from rfl, pow_one, ← Finset.mul_sum]
  have hs := (horizontal_abs_sum_le (fun i => fderiv ℝ f (γ t) (X i (γ t)))).trans
    (mul_le_mul_of_nonneg_left (hH t ht) (Real.sqrt_nonneg _))
  simpa only [mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hs hγ.1.le

end RothschildStein.G1

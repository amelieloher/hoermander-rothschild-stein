-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.RadiusPower

/-! Uniform constants for the weighted Whitney oscillation estimate. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ENNReal

namespace HeatKernel

/-- The explicit Whitney mean-oscillation coefficient has a positive pth root
depending only on dimension, exponent, and the two geometric scale parameters. -/
theorem exists_positive_whitney_coefficient (Q : ℕ) {κ p : ℝ} (hκ : 0 < κ) (hp : 0 < p)
    (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ENNReal.ofReal ((2 : ℝ) ^ p) *
        (ENNReal.ofReal ((3 * (60 * (((2 : ℝ) ^ Q) ^ (1 / p)) ^ 2)) ^ p) *
          ENNReal.ofReal ((5 : ℝ) ^ Q)) *
        ENNReal.ofReal ((2 * (k ^ Q : ℕ) * (2 * r / κ)) ^ (p - 1)) *
        ENNReal.ofReal ((κ + 13) ^ Q) * ENNReal.ofReal r * (1000 ^ Q : ℕ) =
          ENNReal.ofReal ((C * r) ^ p) := by
  let A := (2 : ℝ) ^ p * (3 * (60 * (((2 : ℝ) ^ Q) ^ (1 / p)) ^ 2)) ^ p *
    (5 : ℝ) ^ Q * (κ + 13) ^ Q * (1000 ^ Q : ℕ)
  let J := 4 * (k ^ Q : ℕ) / κ
  have hA : 0 < A := by dsimp only [A]; positivity
  have hJ : 0 < J := by dsimp only [J]; positivity
  refine ⟨(A * J ^ (p - 1)) ^ (1 / p), by positivity, ?_⟩
  intro r hr
  have hR : 2 * (k ^ Q : ℕ) * (2 * r / κ) = J * r := by dsimp only [J]; ring
  have hF : ENNReal.ofReal A = ENNReal.ofReal ((2 : ℝ) ^ p) *
      (ENNReal.ofReal ((3 * (60 * (((2 : ℝ) ^ Q) ^ (1 / p)) ^ 2)) ^ p) *
        ENNReal.ofReal ((5 : ℝ) ^ Q)) * ENNReal.ofReal ((κ + 13) ^ Q) *
        (1000 ^ Q : ℕ) := by
    dsimp only [A]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    simp only [ENNReal.ofReal_natCast]
    ac_rfl
  rw [hR]
  calc
    _ = ENNReal.ofReal A * ENNReal.ofReal ((J * r) ^ (p - 1)) * ENNReal.ofReal r := by
      rw [hF]
      ac_rfl
    _ = _ := ofReal_weighted_radius_eq_root_power hA.le hJ.le hr hp

end HeatKernel

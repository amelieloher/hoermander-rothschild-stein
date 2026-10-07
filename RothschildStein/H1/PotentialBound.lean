-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PotentialGeometry
public import RothschildStein.H1.PotentialSmooth

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Set
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Quantitative decay of the potential, including the factor two from the
quasi-triangle inequality (BB p. 270).
The exponent formulation also applies to first kernel derivatives. -/
theorem fundamentalPotential_bound (ν : G2.HomogeneousNorm G) {a C R : ℝ}
    (ha : a ≤ 0) (hC : 0 ≤ C) {Γ φ : (Fin N → ℝ) → ℝ}
    (hΓ : ∀ z, z ≠ 0 → |Γ z| ≤ C * (ν z) ^ a)
    (hφ : Integrable φ) (hs : ∀ y, φ y ≠ 0 → ν y ≤ R)
    {x : Fin N → ℝ} (hx : x ≠ 0) (hr : 2 * ν.c * R ≤ ν x) :
    |∫ y, Γ (G.mul (G.inv y) x) * φ y| ≤
      C * (2 * ν.c) ^ (-a) * (ν x) ^ a * ∫ y, |φ y| := by
  have hc : 0 < ν.c := lt_of_lt_of_le (by norm_num) ν.one_le_c
  have hxp := G2.gauge_pos ν.gauge hx
  have hfac : (ν x / (2 * ν.c)) ^ a = (2 * ν.c) ^ (-a) * (ν x) ^ a := by
    rw [div_eq_mul_inv, Real.mul_rpow hxp.le (inv_pos.mpr (by positivity)).le,
      Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]
    exact mul_comm _ _
  have hp : ∀ y, ‖Γ (G.mul (G.inv y) x) * φ y‖ ≤
      (C * (2 * ν.c) ^ (-a) * (ν x) ^ a) * |φ y| := by
    intro y
    by_cases hy : φ y = 0
    · simp only [hy, mul_zero, norm_zero, abs_zero, le_refl]
    have hl := potential_distance_lower G ν (hs y hy) hr
    have hz : G.mul (G.inv y) x ≠ 0 := by
      intro hz
      have hzero := (ν.gauge.2.2.1 _).mpr hz
      rw [hzero] at hl
      exact (not_le_of_gt (div_pos hxp (by positivity))) hl
    have hb : |Γ (G.mul (G.inv y) x)| ≤ C * (2 * ν.c) ^ (-a) * (ν x) ^ a := by
      calc
        _ ≤ C * (ν (G.mul (G.inv y) x)) ^ a := hΓ _ hz
        _ ≤ C * (ν x / (2 * ν.c)) ^ a :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (div_pos hxp (by positivity)) hl ha) hC
        _ = _ := by rw [hfac, ← mul_assoc]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have hi := norm_integral_le_of_norm_le
    (hφ.abs.const_mul (C * (2 * ν.c) ^ (-a) * (ν x) ^ a)) (Filter.Eventually.of_forall hp)
  rw [Real.norm_eq_abs, integral_const_mul] at hi
  exact hi

end RothschildStein.H1

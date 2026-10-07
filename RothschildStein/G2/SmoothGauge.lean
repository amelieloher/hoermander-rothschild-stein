-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.SumGauge

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Least common multiple of the positive coordinate weights used in the common-multiple smooth gauge (BB Proposition 3.10, pp. 100–101; Remark 11.35, p. 578). -/
def gaugeLCM : ℕ := Finset.univ.lcm G.weight

private theorem gaugeLCM_pos : 0 < gaugeLCM G := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr fun j _ => ne_of_gt (G.weight_pos j)

private theorem weight_dvd_gaugeLCM (j : Fin N) : G.weight j ∣ gaugeLCM G :=
  Finset.dvd_lcm (Finset.mem_univ j)

/-- The common-multiple polynomial whose root defines the smooth homogeneous norm has even coordinate exponents (BB Remark 11.35, p. 578). -/
def smoothGaugePolynomial (x : Fin N → ℝ) : ℝ :=
  ∑ j, x j ^ (2 * (gaugeLCM G / G.weight j))

/-- Common-multiple smooth gauge (BB pp. 100–101; Remark 11.35, p. 578). -/
def smoothGauge (x : Fin N → ℝ) : ℝ :=
  smoothGaugePolynomial G x ^ ((2 * gaugeLCM G : ℕ) : ℝ)⁻¹

private theorem exponent_eq (j : Fin N) :
    ((2 * gaugeLCM G : ℕ) : ℝ) / (G.weight j : ℝ) =
      ((2 * (gaugeLCM G / G.weight j) : ℕ) : ℝ) := by
  apply (div_eq_iff (Nat.cast_ne_zero.mpr (ne_of_gt (G.weight_pos j)))).mpr
  norm_cast
  rw [mul_assoc, Nat.div_mul_cancel (weight_dvd_gaugeLCM G j)]

/-- The common-multiple polynomial root equals the weighted sum root (BB pp. 100–101). -/
theorem smoothGauge_eq_sumRoot :
    smoothGauge G = sumRootGauge G ((2 * gaugeLCM G : ℕ) : ℝ) := by
  funext x
  unfold smoothGauge smoothGaugePolynomial sumRootGauge
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [exponent_eq, Real.rpow_natCast, pow_abs_two_mul]

/-- The common-multiple smooth gauge is homogeneous (BB Proposition 3.10). -/
theorem isHomogeneousGauge_smoothGauge : G.IsHomogeneousGauge (smoothGauge G) := by
  rw [smoothGauge_eq_sumRoot]
  exact isHomogeneousGauge_sumRoot G _ (by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) (gaugeLCM_pos G))

/-- The polynomial under the root is smooth, including at the origin (BB Remark 11.35, p. 578). -/
theorem contDiff_smoothGaugePolynomial : ContDiff ℝ (⊤ : ℕ∞) (smoothGaugePolynomial G) := by
  unfold smoothGaugePolynomial
  exact ContDiff.sum fun j _ => (contDiff_apply ℝ ℝ j).pow _

/-- The common-multiple smooth gauge is smooth away from the origin (BB pp. 100–101; Remark 11.35, p. 578). -/
theorem contDiffOn_smoothGauge : ContDiffOn ℝ (⊤ : ℕ∞) (smoothGauge G) {0}ᶜ := by
  apply (contDiff_smoothGaugePolynomial G).contDiffOn.rpow_const_of_ne
  intro x hx hzero
  have hz : smoothGauge G x = 0 := by
    unfold smoothGauge
    rw [hzero, Real.zero_rpow]
    exact inv_ne_zero (by exact_mod_cast (Nat.mul_pos (by decide : 0 < 2) (gaugeLCM_pos G)).ne')
  have hx0 : x = 0 := ((isHomogeneousGauge_smoothGauge G).2.2.1 x).mp hz
  exact hx (by simp [hx0])

/-- The common-multiple smooth gauge is even (BB Proposition 3.10, p. 100). -/
theorem smoothGauge_neg (x : Fin N → ℝ) : smoothGauge G (-x) = smoothGauge G x := by
  rw [smoothGauge_eq_sumRoot, sumRootGauge_neg]

end RothschildStein.G2

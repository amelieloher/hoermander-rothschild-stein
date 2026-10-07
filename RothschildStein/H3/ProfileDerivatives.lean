-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TransitionDerivativeBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- Exact affine rescaling formula for each profile derivative. -/
theorem quasiballProfile_iteratedDeriv (j : ℕ) (t s x : ℝ) :
    iteratedDeriv j (quasiballProfile t s) x =
      (-1 : ℝ)^j * (((s - t) / 2)⁻¹)^j *
        iteratedDeriv j Real.smoothTransition (((t + s) / 2 - x) / ((s - t) / 2)) := by
  have he : quasiballProfile t s =
      (fun z => (fun u => Real.smoothTransition (((s - t) / 2)⁻¹ * u))
        ((t + s) / 2 - z)) := by
    funext z
    simp only [quasiballProfile, div_eq_mul_inv, mul_comm]
  rw [he]
  have hs := congrFun (iteratedDeriv_comp_const_sub j
    (fun u : ℝ => Real.smoothTransition (((s - t) / 2)⁻¹ * u)) ((t + s) / 2)) x
  rw [hs]
  rw [iteratedDeriv_comp_const_mul (Real.smoothTransition.contDiff (n := j))]
  simp only [smul_eq_mul, mul_assoc, div_eq_mul_inv]
  congr 3
  exact mul_comm _ _

/-- Uniform scalar derivative constants; the radius dependence is
exactly the inverse gap to the derivative order. -/
theorem exists_quasiballProfile_derivative_bound {j : ℕ} (hj : 0 < j) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ t s : ℝ, t < s → ∀ x : ℝ,
      |iteratedDeriv j (quasiballProfile t s) x| ≤ κ * (2 / (s - t))^j := by
  obtain ⟨κ, hκ, hb⟩ := exists_transition_derivative_bound hj
  refine ⟨κ, hκ, ?_⟩
  intro t s hts x
  have hg : 0 ≤ ((s - t) / 2)⁻¹ := inv_nonneg.mpr (by linarith)
  rw [quasiballProfile_iteratedDeriv, abs_mul, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, one_mul, abs_pow, abs_of_nonneg hg]
  have hi : ((s - t) / 2)⁻¹ = 2 / (s - t) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  rw [hi]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (hb (((t + s) / 2 - x) / ((s - t) / 2)))
      (pow_nonneg (div_nonneg (by norm_num) (sub_nonneg.mpr hts.le)) j)

end RothschildStein.H3

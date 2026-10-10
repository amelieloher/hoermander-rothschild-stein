-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderFiniteIteration
public import HeatKernel.Moser.ReverseHolderNormIteration
public import HeatKernel.Moser.NegativePowerNestedIteration
public import HeatKernel.Moser.NegativePowerCoefficients
import Mathlib.Tactic

/-! Finite reverse-Hölder iteration with the parabolic gap exponent. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Norm steps are needed only while their source exponents lie below the
fixed endpoint. A finite initial norm and an inner measure of mass at most one
give the reverse-Hölder bound, with a constant independent of both exponents. -/
theorem exists_uniform_reverse_holder_initial_finite_iteration_constant
    {C B ν : ℝ} (hC : 1 ≤ C) (hB : 1 ≤ B) (hν : 0 < ν) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {α : Type*} [MeasurableSpace α]
      (μ : Measure α) (μouter : ℕ → Measure α) (f : α → ℝ)
      (δ p p₀ : ℝ), μ Set.univ ≤ 1 →
      0 < δ → δ ≤ 1 → 0 < p → 0 < p₀ → p ≤ p₀ / 2 →
      (∀ j, μ ≤ μouter j) →
      eLpNorm f (ENNReal.ofReal p) (μouter 0) < ⊤ →
      (∀ j, p * (1 + 2 / ν) ^ j ≤ p₀ →
        eLpNorm f (ENNReal.ofReal (p * (1 + 2 / ν) ^ (j + 1))) (μouter (j + 1)) ≤
          ENNReal.ofReal ((C * B ^ j / δ ^ 2) ^ (1 / (p * (1 + 2 / ν) ^ j))) *
            eLpNorm f (ENNReal.ofReal (p * (1 + 2 / ν) ^ j)) (μouter j)) →
      eLpNorm f (ENNReal.ofReal p₀) μ ≤
        ENNReal.ofReal ((K / δ ^ (2 * (ν + 2))) ^ (1 / p - 1 / p₀)) *
          eLpNorm f (ENNReal.ofReal p) (μouter 0) := by
  let K := Real.exp (Real.log C * (ν + 2) + Real.log B * ν * (ν + 2) / 2)
  have hK : 1 ≤ K := Real.one_le_exp_iff.mpr (by
    have := Real.log_nonneg hC
    have := Real.log_nonneg hB
    positivity)
  refine ⟨K, hK, ?_⟩
  intro α _ μ μouter f δ p p₀ hmass hδ hδone hp hp₀ hhalf hμ hfinite hstep
  let χ : ℝ := 1 + 2 / ν
  have hχ : 1 < χ := by
    dsimp only [χ]
    have : 0 < 2 / ν := by positivity
    linarith
  have hχpos : 0 < χ := zero_lt_one.trans hχ
  obtain ⟨n, hn, hn'⟩ := exists_reverse_holder_stopping_index
    (p₀ := p₀) hp (by linarith) hχ
  have htest (j : ℕ) (hj : j ≤ n) : p * χ ^ j ≤ p₀ :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hχ.le hj) hp.le).trans hn
  have hfin : ∀ j ≤ n + 1,
      eLpNorm f (ENNReal.ofReal (p * χ ^ j)) (μouter j) < ⊤ := by
    intro j
    induction j with
    | zero => intro _; simpa only [pow_zero, mul_one] using hfinite
    | succ j ih =>
      intro hj
      exact (hstep j (htest j (by omega))).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ih (by omega)))
  let Y : ℕ → ℝ := fun j => (eLpNorm f (ENNReal.ofReal (p * χ ^ j)) (μouter j)).toReal
  have hA : 0 ≤ Real.log C - 2 * Real.log δ := by
    have := Real.log_nonneg hC
    have := Real.log_nonpos hδ.le hδone
    linarith
  have hreal (j : ℕ) (hj : j < n + 1) : Y (j + 1) ≤
      Real.exp (((Real.log C - 2 * Real.log δ) + Real.log B * j) *
        (χ⁻¹) ^ j / p) * Y j := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin j (by omega))).ne
        (hstep j (htest j (by omega)))
    have hcoef : 0 ≤ (C * B ^ j / δ ^ 2) ^ (1 / (p * χ ^ j)) := by positivity
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoef] at h
    simpa only [Y,
      negative_power_cutoff_factor_eq_exp (zero_lt_one.trans_le hC)
        (zero_lt_one.trans_le hB) hδ hχpos] using h
  have hend := eLpNorm_le_of_reverse_holder_finite_iteration_of_mass_le_one μ hmass
    (inv_nonneg.mpr hχpos.le) ((inv_lt_one₀ hχpos).mpr hχ) hA (Real.log_nonneg hB)
    hp hp₀ hhalf (show 0 ≤ Y 0 from ENNReal.toReal_nonneg) (n + 1) hn'.le
    ((eLpNorm_mono_measure f (hμ (n + 1))).trans
      (le_of_eq (ENNReal.ofReal_toReal (hfin (n + 1) le_rfl).ne).symm)) hreal
  have hnzero : ν + 2 ≠ 0 := by positivity
  have hq : χ⁻¹ = ν / (ν + 2) := by dsimp only [χ]; field_simp [ne_of_gt hν, hnzero]
  obtain ⟨hg, hgj⟩ := negative_power_parabolic_geometric_coefficients hν
  have hcost :
      (Real.log C - 2 * Real.log δ) / (1 - χ⁻¹) +
        Real.log B * χ⁻¹ / (1 - χ⁻¹) ^ 2 =
      (Real.log C - 2 * Real.log δ) * (ν + 2) / 2 + Real.log B * ν * (ν + 2) / 4 := by
    rw [hq]
    calc
      _ = (Real.log C - 2 * Real.log δ) * (1 - ν / (ν + 2))⁻¹ +
          Real.log B * ((ν / (ν + 2)) / (1 - ν / (ν + 2)) ^ 2) := by ring
      _ = _ := by rw [hg, hgj]; ring
  have heq : Real.exp (2 * (1 / p - 1 / p₀) *
      ((Real.log C - 2 * Real.log δ) * (ν + 2) / 2 +
        Real.log B * ν * (ν + 2) / 4)) =
      (K / δ ^ (2 * (ν + 2))) ^ (1 / p - 1 / p₀) := by
    rw [Real.rpow_def_of_pos (by positivity),
      Real.log_div (Real.exp_ne_zero _) (by positivity), Real.log_rpow hδ, Real.log_exp]
    congr 1
    ring
  rw [hcost, heq, ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)] at hend
  simpa only [Y, pow_zero, mul_one, ENNReal.ofReal_toReal hfinite.ne] using hend

end HeatKernel

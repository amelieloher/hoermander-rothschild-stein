-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierDefs
public import RothschildStein.S.WordLeibniz
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The large-radius anisotropic cutoff ψ(D_{1/R}x)
(BB Thm 3.49 proof, p. 123). -/
def groupSobolevCutoff (ψ : (Fin N → ℝ) → ℝ) (R : ℝ) (x : Fin N → ℝ) : ℝ :=
  ψ (G.dilate R⁻¹ x)

/-- A cutoff equal to one on the gauge unit ball is eventually
one at each fixed point (BB Thm 3.49 proof, p. 123). -/
theorem groupSobolevCutoff_eventually_eq_one (ν : HomogeneousNorm G)
    {ψ : (Fin N → ℝ) → ℝ} (hψ : ∀ x, ν x ≤ 1 → ψ x = 1) (x : Fin N → ℝ) :
    ∀ᶠ R : ℝ in atTop, groupSobolevCutoff G ψ R x = 1 := by
  filter_upwards [eventually_ge_atTop (max 1 (ν x))] with R hR
  have hpos : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
  apply hψ
  rw [ν.gauge.2.2.2 R⁻¹ (inv_pos.mpr hpos) x]
  calc
    _ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hR)
      (inv_nonneg.mpr hpos.le)
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- The empty-word part of cutoff approximation converges in Lp
for every finite positive exponent (BB Thm 3.49 proof, p. 123). -/
theorem tendsto_groupSobolevCutoff_mul_eLpNorm (ν : HomogeneousNorm G)
    {ψ f : (Fin N → ℝ) → ℝ} (hψ : Continuous ψ)
    (hψbound : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (hψone : ∀ x, ν x ≤ 1 → ψ x = 1)
    {p : ℝ} (hp : 0 < p) (hf : MemLp f (ENNReal.ofReal p) volume) :
    Tendsto (fun R : ℝ => eLpNorm (fun x => f x * groupSobolevCutoff G ψ R x - f x)
      (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hmeas (R : ℝ) : AEStronglyMeasurable
      (fun x => f x * groupSobolevCutoff G ψ R x - f x) volume :=
    (hf.aestronglyMeasurable.mul (hψ.comp (continuous_dilate G R⁻¹)).aestronglyMeasurable).sub
      hf.aestronglyMeasurable
  have hnorm (R : ℝ) (x : Fin N → ℝ) :
      ‖f x * groupSobolevCutoff G ψ R x - f x‖ₑ ≤ ‖f x‖ₑ := by
    have hb := hψbound (G.dilate R⁻¹ x)
    have hreal : ‖f x * groupSobolevCutoff G ψ R x - f x‖ ≤ ‖f x‖ := by
      rw [show f x * groupSobolevCutoff G ψ R x - f x =
        f x * (ψ (G.dilate R⁻¹ x) - 1) by unfold groupSobolevCutoff; ring, norm_mul]
      have hdiff : ‖ψ (G.dilate R⁻¹ x) - 1‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        linarith
      exact (mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)).trans_eq (mul_one _)
    simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hreal
  have hfin : (∫⁻ x, ‖f x‖ₑ ^ p) ≠ ⊤ := by
    have H := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top hf.eLpNorm_lt_top
    simpa only [ENNReal.toReal_ofReal hp.le] using H.ne
  have ht : ∀ᵐ x ∂volume, Tendsto
      (fun R : ℝ => ‖f x * groupSobolevCutoff G ψ R x - f x‖ₑ ^ p) atTop (𝓝 (0 : ℝ≥0∞)) := by
    apply Eventually.of_forall
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [groupSobolevCutoff_eventually_eq_one G ν hψone x] with R hR
    simp only [hR, mul_one, sub_self, enorm_zero, ENNReal.zero_rpow_of_pos hp]
  have H := tendsto_lintegral_filter_of_dominated_convergence' (fun x => ‖f x‖ₑ ^ p)
    (Eventually.of_forall fun R => (hmeas R).enorm.pow_const p)
    (Eventually.of_forall fun R => Eventually.of_forall fun x =>
      ENNReal.rpow_le_rpow (hnorm R x) hp.le) hfin ht
  have Hpow := H.ennrpow_const (1 / p)
  have he (R : ℝ) := eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top (hmeas R)
  simp only [ENNReal.toReal_ofReal hp.le] at he
  simpa only [← he, lintegral_zero, ENNReal.zero_rpow_of_pos (div_pos zero_lt_one hp)] using Hpow

end RothschildStein.G2

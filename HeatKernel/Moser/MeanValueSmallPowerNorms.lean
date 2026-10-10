-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSmallPowerInterpolation
public import HeatKernel.Moser.MeanValueSmallPowerIteration
import Mathlib.Tactic

/-! # Small-power norm bounds from nested quadratic mean values -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Quadratic mean values with geometric gap losses imply each fixed smaller
positive-power bound. The common outer measure, measurability, quadratic steps
and finite uniform supremum on the truncated family are explicit hypotheses;
the resulting constant is independent of that finite supremum. -/
theorem exists_small_power_constant_of_quadratic_iteration
    {α : Type*} [MeasurableSpace α] {p F B : ℝ}
    (hp : 0 < p) (hp2 : p < 2) (hF : 0 < F) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μouter : Measure α) (μ : ℕ → Measure α) (f : α → ℝ),
      (∀ j, μ j ≤ μouter) → (∀ j, AEStronglyMeasurable f (μ j)) →
      (∃ H : ℝ, ∀ j, eLpNormEssSup f (μ j) ≤ ENNReal.ofReal H) →
      (∀ j, eLpNormEssSup f (μ j) ≤ ENNReal.ofReal (F * B ^ j) *
        eLpNorm f 2 (μ (j + 1))) →
      eLpNormEssSup f (μ 0) ≤ ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) μouter := by
  let θ := 1 - p / 2
  have hθ : 0 < θ := by dsimp only [θ]; linarith
  have hθone : θ < 1 := by dsimp only [θ]; linarith
  let A := B ^ (1 / (1 - θ))
  let ε := (2 * A)⁻¹
  let C := 2 * (F / ε ^ θ) ^ (1 / (1 - θ))
  have hA : 0 < A := Real.rpow_pos_of_pos (by linarith) _
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hC : 0 < C := mul_pos (by norm_num)
    (Real.rpow_pos_of_pos (div_pos hF (Real.rpow_pos_of_pos hε _)) _)
  refine ⟨C, hC, ?_⟩
  intro μouter μ f hμ hf hbounded hquad
  obtain ⟨H, hH⟩ := hbounded
  let S := fun j => (eLpNormEssSup f (μ j)).toReal
  let N := (eLpNorm f (ENNReal.ofReal p) μouter).toReal
  have hfinite (j : ℕ) : eLpNormEssSup f (μ j) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hH j)
  by_cases htop : eLpNorm f (ENNReal.ofReal p) μouter = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hC).ne']
    exact le_top
  have hnormstep (j : ℕ) :
      S j ≤ F * B ^ j * S (j + 1) ^ θ * N ^ (1 - θ) := by
    have hi := eLpNorm_two_le_small_power_of_ae_bound (μ (j + 1))
      (hf (j + 1)) (ae_le_eLpNormEssSup (f := f)) hp hp2
    have hn := eLpNorm_mono_measure (p := ENNReal.ofReal p) f (hμ (j + 1))
    have h := (hquad j).trans (mul_le_mul' le_rfl
      (hi.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hn (by positivity : 0 ≤ p / 2)))))
    have hrhs : ENNReal.ofReal (F * B ^ j) *
        (eLpNormEssSup f (μ (j + 1)) ^ (1 - p / 2) *
          eLpNorm f (ENNReal.ofReal p) μouter ^ (p / 2)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) (hfinite _))
          (ENNReal.rpow_ne_top_of_nonneg (by positivity) htop))
    have hreal := ENNReal.toReal_mono hrhs h
    have hcoef : 0 ≤ F * B ^ j := mul_nonneg hF.le (pow_nonneg (by linarith) _)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_rpow, ENNReal.toReal_ofReal hcoef,
      S, N, θ, show 1 - (1 - p / 2) = p / 2 by ring, mul_assoc] using hreal
  have hbound (j : ℕ) : S j ≤ (ENNReal.ofReal H).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top (hH j)
  have h := le_of_bounded_mixed_power_iteration hF.le hB
    (show 0 ≤ N from ENNReal.toReal_nonneg) hθ hθone
    (fun j => ENNReal.toReal_nonneg) hnormstep hbound
  change S 0 ≤ C * N at h
  calc
    eLpNormEssSup f (μ 0) = ENNReal.ofReal (S 0) :=
      (ENNReal.ofReal_toReal (hfinite 0)).symm
    _ ≤ ENNReal.ofReal (C * N) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) μouter := by
      rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal htop]

end HeatKernel

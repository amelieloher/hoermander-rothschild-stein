-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HarnackPowerScaling
import Mathlib.Tactic

/-! # Assembly of logarithmic and power families with a common shift

The earlier reverse Hölder family and later reciprocal mean-value family are
homogeneous. Their constants therefore remain unchanged when the shift is
chosen by the two signed logarithmic tails.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Unshifted power families and logarithmic tails supply the local estimates
with one shared logarithmic shift and separating time for each perturbation. -/
theorem hasHarnackCylinderEstimates_of_unshifted_families
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    (μ : Measure (ℝ × E)) (x : E) (t r : ℝ) (u : ℝ × E → ℝ)
    {p₀ Aminus Aplus Cminus Cplus κminus κplus : ℝ} (hp₀ : 0 < p₀)
    (hlog : ∀ ε : ℝ, 0 < ε → ∃ τ c : ℝ,
      t - 113 / 64 * r ^ 2 < τ ∧ τ < t - 111 / 64 * r ^ 2 ∧
      (∀ ℓ : ℝ, 0 < ℓ →
        μ ((Ioo (t - 225 / 64 * r ^ 2) τ ×ˢ Metric.ball x (5 / 4 * r)) ∩
          {y | c + ℓ < Real.log (u y + ε)}) ≤ ENNReal.ofReal (Aminus / ℓ) *
            μ (Ioo (t - 225 / 64 * r ^ 2) τ ×ˢ Metric.ball x (5 / 4 * r))) ∧
      (∀ ℓ : ℝ, 0 < ℓ →
        μ ((Ioo τ t ×ˢ Metric.ball x (5 / 4 * r)) ∩
          {y | Real.log (u y + ε) < c - ℓ}) ≤ ENNReal.ofReal (Aplus / ℓ) *
            μ (Ioo τ t ×ˢ Metric.ball x (5 / 4 * r))))
    (hreverse : ∀ ε : ℝ, 0 < ε →
      ∀ σ' σ'' : ℝ, 31 / 32 ≤ σ' → σ' < σ'' → σ'' ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      (∫⁻ y in harnackEarlierIterationCylinder x t r σ',
        ENNReal.ofReal (u y + ε) ^ p₀ ∂μ) ^ (1 / p₀) ≤
        (ENNReal.ofReal (Cminus * (1 / (σ'' - σ')) ^ κminus) *
          (μ (harnackEarlierIterationCylinder x t r 1))⁻¹) ^ (1 / p - 1 / p₀) *
            (∫⁻ y in harnackEarlierIterationCylinder x t r σ'',
              ENNReal.ofReal (u y + ε) ^ p ∂μ) ^ (1 / p))
    (hreciprocal : ∀ ε : ℝ, 0 < ε →
      ∀ σ' σ'' : ℝ, 9 / 10 ≤ σ' → σ' < σ'' → σ'' ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      essSup (fun y => ENNReal.ofReal (1 / (u y + ε)))
        (μ.restrict (harnackLaterIterationCylinder x t r σ')) ≤
        (ENNReal.ofReal (Cplus * (1 / (σ'' - σ')) ^ κplus) *
          (μ (harnackLaterIterationCylinder x t r 1))⁻¹ *
            (∫⁻ y in harnackLaterIterationCylinder x t r σ'',
              ENNReal.ofReal (1 / (u y + ε)) ^ p ∂μ)) ^ (1 / p)) :
    HasHarnackCylinderEstimates μ x t r p₀
      Aminus Aplus Cminus Cplus κminus κplus u := by
  intro ε hε
  obtain ⟨τ, c, hτlower, hτupper, hminus, hplus⟩ := hlog ε hε
  refine ⟨τ, c, hτlower, hτupper, hminus, hplus, ?_, ?_⟩
  · intro σ' σ'' hθ hgap hσone p hp hptop
    have he := reverseHolder_moment_bound_const_mul μ
      (fun y => ENNReal.ofReal (u y + ε))
      (harnackEarlierIterationCylinder x t r σ')
      (harnackEarlierIterationCylinder x t r σ'') hp hp₀
      (c := ENNReal.ofReal (Real.exp (-c))) ENNReal.ofReal_ne_top
      (hreverse ε hε σ' σ'' hθ hgap hσone p hp hptop)
    simpa only [← ENNReal.ofReal_mul (Real.exp_pos _).le] using he
  · intro σ' σ'' hθ hgap hσone p hp hptop
    have he := essSup_moment_bound_const_mul μ
      (fun y => ENNReal.ofReal (1 / (u y + ε)))
      (harnackLaterIterationCylinder x t r σ')
      (harnackLaterIterationCylinder x t r σ'') hp
      (c := ENNReal.ofReal (Real.exp c)) ENNReal.ofReal_ne_top
      (hreciprocal ε hε σ' σ'' hθ hgap hσone p hp hptop)
    simpa only [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_one_div] using he

end HeatKernel

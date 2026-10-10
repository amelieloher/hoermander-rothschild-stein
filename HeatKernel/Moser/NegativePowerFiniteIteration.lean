-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerParabolicIteration
public import HeatKernel.Moser.MeanValueFiniteIteration

/-! Reciprocal iteration from a single finite initial moment. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- An extended norm recurrence propagates finiteness from any positive initial
exponent and yields a uniform parabolic essential bound. -/
theorem exists_uniform_negative_power_initial_finite_iteration_constant
    {C B ν : ℝ} (hC : 1 ≤ C) (hB : 1 ≤ B) (hν : 0 < ν) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {α : Type*} [MeasurableSpace α]
      (μ : Measure α) (μouter : ℕ → Measure α) (f : α → ℝ)
      (δ p : ℝ), 0 < δ → δ ≤ 1 → 0 < p →
      (∀ j, μ ≤ μouter j) →
      eLpNorm f (ENNReal.ofReal p) (μouter 0) < ⊤ →
      (∀ j, eLpNorm f (ENNReal.ofReal (p * (1 + 2 / ν) ^ (j + 1)))
          (μouter (j + 1)) ≤
        ENNReal.ofReal ((C * B ^ j / δ ^ 2) ^ (1 / (p * (1 + 2 / ν) ^ j))) *
          eLpNorm f (ENNReal.ofReal (p * (1 + 2 / ν) ^ j)) (μouter j)) →
      eLpNormEssSup f μ ≤ ENNReal.ofReal ((K / δ ^ (ν + 2)) ^ (1 / p) *
        (eLpNorm f (ENNReal.ofReal p) (μouter 0)).toReal) := by
  obtain ⟨K, hK, hiter⟩ := exists_uniform_negative_power_iteration_constant hC hB hν
  refine ⟨K, hK, ?_⟩
  intro α _ μ μouter f δ p hδ hδone hp hμ hfinite hstep
  have hfin : ∀ j, eLpNorm f (ENNReal.ofReal (p * (1 + 2 / ν) ^ j))
      (μouter j) < ⊤ :=
    ennreal_lt_top_of_mul_recurrence (by simpa using hfinite)
      (fun _ => ENNReal.ofReal_lt_top) hstep
  have hbound := hiter μ μouter f
    (fun j => (eLpNorm f (ENNReal.ofReal (p * (1 + 2 / ν) ^ j))
      (μouter j)).toReal) δ p hδ hδone hp ENNReal.toReal_nonneg hμ
    (fun j => le_of_eq (ENNReal.ofReal_toReal (hfin j).ne).symm) (fun j => ?_)
  · simpa only [pow_zero, mul_one] using hbound
  · have hcoef : 0 ≤ (C * B ^ j / δ ^ 2) ^
        (1 / (p * (1 + 2 / ν) ^ j)) := Real.rpow_nonneg (by positivity) _
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin j)).ne (hstep j)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoef] using hreal

end HeatKernel

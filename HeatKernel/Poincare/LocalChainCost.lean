-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Linarith

/-! Restricting local Whitney oscillation bounds to a chain's starting domain. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal

namespace HeatKernel

/-- Restricting the oscillation and enlarging the reference volume puts a local
energy cost in the normalization used by the chain estimate. -/
theorem eLpNorm_restrict_le_normalized_chain_cost {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → ℝ) {A U V : Set E} (hAU : A ⊆ U) (hUV : U ⊆ V)
    {p a L K : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hK : 0 ≤ K) (hLK : L ≤ K)
    (h : ℝ≥0)
    (hlocal : eLpNorm f (ENNReal.ofReal p) (μ.restrict V) ≤
      ENNReal.ofReal (L * a) * μ A ^ (1 / p) * h) :
    eLpNorm f (ENNReal.ofReal p) (μ.restrict U) ≤
      ENNReal.ofReal (K * (a * (h : ℝ))) * μ U ^ (1 / p) := by
  have hc := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hLK ha)
  have hv : μ A ^ (1 / p) ≤ μ U ^ (1 / p) :=
    ENNReal.rpow_le_rpow (measure_mono hAU) (one_div_nonneg.mpr hp.le)
  calc
    _ ≤ eLpNorm f (ENNReal.ofReal p) (μ.restrict V) :=
      eLpNorm_mono_measure f (Measure.restrict_mono hUV le_rfl)
    _ ≤ ENNReal.ofReal (L * a) * μ A ^ (1 / p) * h := hlocal
    _ ≤ ENNReal.ofReal (K * a) * μ A ^ (1 / p) * h :=
      mul_le_mul_left (mul_le_mul_left hc _) _
    _ ≤ ENNReal.ofReal (K * a) * μ U ^ (1 / p) * h :=
      mul_le_mul_left (mul_le_mul_right hv _) _
    _ = _ := by
      rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_mul hK, ENNReal.ofReal_mul ha,
        ENNReal.ofReal_coe_nnreal]
      ac_rfl

/-- The homogeneous edge coefficient dominates the coefficient of the local
twentyfold averaging estimate. -/
theorem local_homogeneous_coefficient_le_edge_coefficient (Q : ℕ) {p : ℝ} (hp : 0 < p) :
    60 * ((2 : ℝ) ^ Q) ^ (1 / p) ≤ 60 * (((2 : ℝ) ^ Q) ^ (1 / p)) ^ 2 := by
  have ht : 1 ≤ ((2 : ℝ) ^ Q) ^ (1 / p) :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num)) (one_div_nonneg.mpr hp.le)
  nlinarith

end HeatKernel

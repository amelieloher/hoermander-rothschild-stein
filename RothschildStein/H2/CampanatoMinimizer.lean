-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.Patches
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Lipschitz
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Absolute integral oscillation about a constant (BB p. 328). -/
def integralOscillation (μ : Measure X) (u : X → ℝ) (c : ℝ) : ℝ :=
  ∫ y, |u y - c| ∂μ

/-- The oscillation is Lipschitz in the constant. -/
theorem integralOscillation_lipschitz {μ : Measure X} [IsFiniteMeasure μ]
    {u : X → ℝ} (hu : Integrable u μ) :
    LipschitzWith (μ univ).toNNReal (integralOscillation μ u) := by
  apply LipschitzWith.of_dist_le_mul
  intro c d
  rw [Real.dist_eq, Real.dist_eq]
  change |(∫ y, |u y - c| ∂μ) - ∫ y, |u y - d| ∂μ| ≤ _
  have huc : Integrable (fun y => |u y - c|) μ := (hu.sub (integrable_const c)).abs
  have hud : Integrable (fun y => |u y - d|) μ := (hu.sub (integrable_const d)).abs
  rw [← integral_sub huc hud]
  calc
    _ ≤ ∫ y, abs (|u y - c| - |u y - d|) ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := μ) (fun y => |u y - c| - |u y - d|)
    _ ≤ ∫ _ : X, |c - d| ∂μ := by
      apply integral_mono ((hu.sub (integrable_const c)).abs.sub
        (hu.sub (integrable_const d)).abs).abs (integrable_const _)
      intro y
      have ht := abs_abs_sub_abs_le_abs_sub (u y - c) (u y - d)
      have he : (u y - c) - (u y - d) = -(c - d) := by ring
      rwa [he, abs_neg] at ht
    _ = (μ univ).toNNReal * |c - d| := by
      simp only [integral_const, smul_eq_mul, ENNReal.coe_toNNReal_eq_toReal, measureReal_def]

/-- Coercive lower bound for the oscillation. -/
theorem integralOscillation_coercive {μ : Measure X} [IsFiniteMeasure μ]
    {u : X → ℝ} (hu : Integrable u μ) (c : ℝ) :
    |c| * (μ univ).toReal - ∫ y, |u y| ∂μ ≤ integralOscillation μ u c := by
  have h := integral_mono (integrable_const |c|)
    ((hu.sub (integrable_const c)).abs.add hu.abs)
    (fun y => show |c| ≤ |u y - c| + |u y| by
      have ht := abs_add_le (c - u y) (u y)
      rw [sub_add_cancel] at ht
      simpa only [abs_sub_comm c (u y)] using ht)
  dsimp only [Pi.add_apply, Pi.sub_apply] at h
  rw [integral_add (show Integrable (fun y => |u y - c|) μ from (hu.sub (integrable_const c)).abs) hu.abs,
    integral_const, smul_eq_mul] at h
  change (μ univ).toReal * |c| ≤ _ at h
  change _ ≤ ∫ y, |u y - c| ∂μ
  nlinarith

/-- A positive finite measure gives an attained minimum.
This fills the minimiser choice in BB p. 328 without assuming uniqueness. -/
theorem exists_integralOscillation_minimizer {μ : Measure X} [IsFiniteMeasure μ]
    (hμ : 0 < μ univ) {u : X → ℝ} (hu : Integrable u μ) :
    ∃ c : ℝ, ∀ d : ℝ, integralOscillation μ u c ≤ integralOscillation μ u d := by
  have hm : 0 < (μ univ).toReal := ENNReal.toReal_pos hμ.ne' (measure_ne_top _ _)
  let I := ∫ y, |u y| ∂μ
  have hI : 0 ≤ I := integral_nonneg fun _ => abs_nonneg _
  let K := 2 * I / (μ univ).toReal + 1
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨c, hc, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (-K) K).Nonempty from ⟨0, by constructor <;> linarith⟩)
    (integralOscillation_lipschitz hu).continuous.continuousOn
  refine ⟨c, fun d => ?_⟩
  by_cases hd : d ∈ Icc (-K) K
  · exact hmin hd
  · have hdK : K < |d| := by
      simp only [mem_Icc, not_and_or, not_le] at hd
      rcases hd with hd | hd
      · exact (by linarith : K < -d).trans_le (neg_le_abs d)
      · exact hd.trans_le (le_abs_self d)
    have hz := hmin (show (0 : ℝ) ∈ Icc (-K) K by constructor <;> linarith)
    have hco := integralOscillation_coercive hu d
    have he : K * (μ univ).toReal = 2 * I + (μ univ).toReal := by
      dsimp [K]; field_simp
    have hmul := mul_lt_mul_of_pos_right hdK hm
    have hzero : integralOscillation μ u 0 = I := by simp [integralOscillation, I]
    change integralOscillation μ u c ≤ integralOscillation μ u 0 at hz
    rw [hzero] at hz
    linarith
end RothschildStein.H2

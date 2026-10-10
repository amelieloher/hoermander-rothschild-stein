-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.SignedAveragingKernel
public import HeatKernel.Sobolev.BallAveraging
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! # Signed real ball averages and their L¹-to-L² estimate -/

@[expose] public section
open MeasureTheory Set Metric
open scoped ENNReal NNReal
namespace HeatKernel.Sobolev

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
    [SecondCountableTopology α] {μ : Measure α} [SFinite μ]

/-- Signed ball averages are measurable as functions of their centers. -/
theorem measurable_signed_ballAverage (s : ℝ) (V : ℝ≥0∞)
    {f : α → ℝ} (hf : Measurable f) :
    Measurable (fun x => (∫ y in ball x s, f y ∂μ) / V.toReal) := by
  have hm : Measurable (fun z : α × α => if dist z.1 z.2 < s then f z.2 else 0) :=
    Measurable.ite (measurableSet_lt measurable_dist measurable_const)
      (hf.comp measurable_snd) measurable_const
  have H := (hm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have he : (fun x => ∫ y, (if dist x y < s then f y else 0) ∂μ) =
      fun x => ∫ y in ball x s, f y ∂μ := by
    funext x
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by simp only [indicator, mem_ball, dist_comm])
  rw [he] at H
  exact H.div_const V.toReal

/-- The quadratic integral of a signed ball average is bounded by the squared absolute mass. -/
theorem lintegral_signed_ballAverage_sq_le {s : ℝ} {V : ℝ≥0∞}
    (hV : V ≠ 0) (hVtop : V ≠ ⊤) (hvolume : ∀ x : α, μ (ball x s) = V)
    {f : α → ℝ} (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal (((∫ y in ball x s, f y ∂μ) / V.toReal) ^ 2) ∂μ) ≤
      V⁻¹ * (∫⁻ y, ENNReal.ofReal |f y| ∂μ) ^ 2 := by
  let j : α → α → ℝ := fun x y => if dist x y < s then V.toReal⁻¹ else 0
  have hinv : ENNReal.ofReal |V.toReal⁻¹| = V⁻¹ := by
    rw [abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg),
      ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hV hVtop), ENNReal.ofReal_toReal hVtop]
  have hmajorant : ∀ x y, ENNReal.ofReal |j x y| ≤ ballAverageKernel s V x y := by
    intro x y
    dsimp only [j, ballAverageKernel]
    split_ifs with hxy
    · exact hinv.le
    · simp
  have H := lintegral_signed_averageKernel_sq_le (μ := μ) (c := V⁻¹) (measurable_ballAverageKernel s V)
    hmajorant (fun y => (lintegral_ballAverageKernel_eq_one hV hVtop hvolume y).le)
    (fun x y => by unfold ballAverageKernel; split_ifs <;> simp) hf
  have he (x : α) : (∫ y, j x y * f y ∂μ) = (∫ y in ball x s, f y ∂μ) / V.toReal := by
    have hj : (fun y => j x y * f y) =
        (ball x s).indicator (fun y => V.toReal⁻¹ * f y) := by
      funext y
      by_cases hy : dist x y < s <;> simp [j, indicator, mem_ball, dist_comm, hy]
    rw [hj, integral_indicator measurableSet_ball, integral_const_mul]
    ring
  simpa only [he] using H

/-- Signed real ball averages satisfy the squared L¹-to-L² norm estimate. -/
theorem eLpNorm_signed_ballAverage_sq_le {s : ℝ} {V : ℝ≥0∞}
    (hV : V ≠ 0) (hVtop : V ≠ ⊤) (hvolume : ∀ x : α, μ (ball x s) = V)
    {f : α → ℝ} (hf : Measurable f) :
    eLpNorm (fun x => (∫ y in ball x s, f y ∂μ) / V.toReal) 2 μ ^ 2 ≤
      V⁻¹ * eLpNorm f 1 μ ^ 2 := by
  have hm : AEStronglyMeasurable (fun x => (∫ y in ball x s, f y ∂μ) / V.toReal) μ :=
    (measurable_signed_ballAverage (μ := μ) s V hf).aestronglyMeasurable
  have he := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hm
  norm_num only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at he
  simp_rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs] at he
  rw [he, eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
  simpa only [Real.enorm_eq_ofReal_abs] using lintegral_signed_ballAverage_sq_le hV hVtop hvolume hf

end HeatKernel.Sobolev

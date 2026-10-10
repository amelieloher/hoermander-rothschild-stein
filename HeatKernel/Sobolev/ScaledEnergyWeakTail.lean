-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.ScaledEnergyWeakFromNormNash
public import HeatKernel.Sobolev.SobolevFromNash
import Mathlib.Tactic

/-! # Extended weak tails with radius-scaled energy -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- Positive superlevel sets of a zero-boundary graph value have finite measure. -/
theorem measure_abs_gt_ne_top_zeroBoundaryGraph {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hfinite : volume (U : Set (Fin N → ℝ)) ≠ ⊤)
    (v : zeroBoundaryGraph U X) {s : ℝ} (hs : 0 < s) :
    volume {x | s < |(v : GradientSpace (N := N) ⊤ q).fst x|} ≠ ⊤ := by
  apply ne_top_of_le_ne_top hfinite
  apply measure_mono_ae
  filter_upwards [ae_eq_zero_outside_of_mem_zeroBoundaryGraph U X v] with x hx
  intro htail
  by_contra hout
  change s < |(v : GradientSpace (N := N) ⊤ q).fst x| at htail
  rw [hx hout, abs_zero] at htail
  linarith

/-- The energy factor in a weak Nash tail separates with the weak Sobolev exponent. -/
theorem weakSobolevConstant_energy_factor {C S b : ℝ}
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hb : b < 1) :
    (2 ^ weakSobolevExponent b * (C * S ^ (1 - b / 2))) ^ (1 / (1 - b)) =
      weakSobolevConstant C b * S ^ (weakSobolevExponent b / 2) := by
  have he : (1 - b / 2) * (1 / (1 - b)) = weakSobolevExponent b / 2 := by
    unfold weakSobolevExponent
    have hd : 1 - b ≠ 0 := by linarith
    field_simp
  rw [← mul_assoc, Real.mul_rpow
    (mul_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) _) hC)
    (Real.rpow_nonneg hS _), ← Real.rpow_mul hS, he]
  rfl

/-- Scaled norm-form Nash gives an extended-measure tail with its energy factor explicit. -/
theorem measure_abs_gt_le_scaled_energy_power_of_nash {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hfinite : volume (U : Set (Fin N → ℝ)) ≠ ⊤)
    (r : ℝ) {C b : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b) (hb₁ : b < 1)
    (hnash : ∀ z : zeroBoundaryGraph U X,
      ‖(z : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤ C *
        (r ^ 2 * ‖(z : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
          ‖(z : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ^ (1 - b / 2) *
        (eLpNorm (z : GradientSpace (N := N) ⊤ q).fst 1 volume).toReal ^ b)
    (v : zeroBoundaryGraph U X) {s : ℝ} (hs : 0 < s) :
    volume {x | s < |(v : GradientSpace (N := N) ⊤ q).fst x|} ≤
      ENNReal.ofReal ((weakSobolevConstant C b *
        (r ^ 2 * ‖(v : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
          ‖(v : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ^ (weakSobolevExponent b / 2)) *
        s ^ (-weakSobolevExponent b)) := by
  have ha : 0 ≤ 1 - b / 2 := by linarith
  have H := measure_abs_gt_le_on_zeroBoundaryGraph_of_scaled_norm_nash U X hX hfinite r
    hC ha hb hb₁ hnash v hs
  change volume.real {x | s < |(v : GradientSpace (N := N) ⊤ q).fst x|} ≤
    (2 ^ weakSobolevExponent b * (C *
      (r ^ 2 * ‖(v : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(v : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ^ (1 - b / 2))) ^ (1 / (1 - b)) *
      s ^ (-weakSobolevExponent b) at H
  rw [weakSobolevConstant_energy_factor hC (by positivity) hb₁] at H
  have h := ENNReal.ofReal_le_ofReal H
  simpa only [Measure.real, ENNReal.ofReal_toReal
    (measure_abs_gt_ne_top_zeroBoundaryGraph U X hfinite v hs)] using h

end HeatKernel.Sobolev

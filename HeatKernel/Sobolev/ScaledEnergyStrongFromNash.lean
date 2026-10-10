-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.ScaledEnergyWeakTail
import Mathlib.Tactic

/-! # Strong subcritical estimates with radius-scaled horizontal energy -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- A scaled Nash bound on the zero-boundary domain yields a strong subcritical bound there. -/
theorem eLpNorm_sq_le_scaled_energy_of_nash {N k : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hfinite : volume (U : Set (Fin N → ℝ)) ≠ ⊤)
    (r : ℝ) {C b p : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b) (hb₁ : b < 1)
    (hp : 2 < p) (hpp : p < weakSobolevExponent b)
    (hnash : ∀ z : zeroBoundaryGraph U X,
      ‖(z : GradientSpace (N := N) ⊤ k).fst‖ ^ 2 ≤ C *
        (r ^ 2 * ‖(z : GradientSpace (N := N) ⊤ k).snd‖ ^ 2 +
          ‖(z : GradientSpace (N := N) ⊤ k).fst‖ ^ 2) ^ (1 - b / 2) *
        (eLpNorm (z : GradientSpace (N := N) ⊤ k).fst 1 volume).toReal ^ b)
    (v : zeroBoundaryGraph U X) :
    eLpNorm (v : GradientSpace (N := N) ⊤ k).fst (ENNReal.ofReal p) volume ^ 2 ≤
      ENNReal.ofReal (subcriticalSobolevConstant C b p *
        (r ^ 2 * ‖(v : GradientSpace (N := N) ⊤ k).snd‖ ^ 2 +
          ‖(v : GradientSpace (N := N) ⊤ k).fst‖ ^ 2)) := by
  have hv : MemLp (v : GradientSpace (N := N) ⊤ k).fst 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp (v : GradientSpace (N := N) ⊤ k).fst
  have hS : 0 ≤ r ^ 2 * ‖(v : GradientSpace (N := N) ⊤ k).snd‖ ^ 2 +
      ‖(v : GradientSpace (N := N) ⊤ k).fst‖ ^ 2 := by positivity
  have hK : 0 ≤ weakSobolevConstant C b := by
    unfold weakSobolevConstant
    positivity
  have hmoment : (∫ x, (v : GradientSpace (N := N) ⊤ k).fst x ^ 2) =
      ‖(v : GradientSpace (N := N) ⊤ k).fst‖ ^ 2 := by
    have H := norm_sq_eq_integral_sq_of_ae_eq (v : GradientSpace (N := N) ⊤ k).fst
      (Filter.Eventually.of_forall fun _ => rfl)
    simpa only [Opens.coe_top, Measure.restrict_univ] using H.symm
  have hL₂ : (∫ x, (v : GradientSpace (N := N) ⊤ k).fst x ^ 2) ≤
      r ^ 2 * ‖(v : GradientSpace (N := N) ⊤ k).snd‖ ^ 2 +
        ‖(v : GradientSpace (N := N) ⊤ k).fst‖ ^ 2 := by
    rw [hmoment]
    exact le_add_of_nonneg_left (mul_nonneg (sq_nonneg r) (sq_nonneg _))
  exact eLpNorm_sq_le_energy_of_weak_tail hv hS hK hp hpp hL₂
    (fun _ hs => measure_abs_gt_le_scaled_energy_power_of_nash U X hX hfinite r
      hC hb hb₁ hnash v hs)

end HeatKernel.Sobolev

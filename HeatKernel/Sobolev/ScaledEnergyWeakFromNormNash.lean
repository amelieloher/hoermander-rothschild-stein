-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.ScaledEnergyWeakFromNash
public import HeatKernel.Sobolev.LebesgueMoments
import Mathlib.Tactic

/-! # Weak distribution estimates from scaled norm-form Nash inequalities -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- A norm-form Nash inequality on the zero-boundary domain implies the weak power bound. -/
theorem measure_abs_gt_le_on_zeroBoundaryGraph_of_scaled_norm_nash {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hfinite : volume (U : Set (Fin N → ℝ)) ≠ ⊤)
    (r : ℝ) {C a b : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hb₁ : b < 1)
    (hnash : ∀ z : zeroBoundaryGraph U X,
      ‖(z : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤ C * (r ^ 2 * ‖(z : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(z : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ^ a *
        (eLpNorm (z : GradientSpace (N := N) ⊤ q).fst 1 volume).toReal ^ b)
    (v : zeroBoundaryGraph U X) {s : ℝ} (hs : 0 < s) :
    volume.real {x | s < |(v : GradientSpace (N := N) ⊤ q).fst x|} ≤
      (2 ^ ((2 - b) / (1 - b)) * (C * (r ^ 2 * ‖(v : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(v : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ^ a)) ^ (1 / (1 - b)) *
        s ^ (-((2 - b) / (1 - b))) := by
  apply measure_abs_gt_le_on_zeroBoundaryGraph_of_scaled_nash U X hX hfinite r hC ha hb hb₁ _ v hs
  intro z f _ hrep hnonneg
  have hf₁ : MemLp f 1 volume := (memLp_congr_ae hrep).mp
    (memLp_one_zeroBoundaryGraph U X hfinite z).1
  have hrep' : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict
      ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))] f := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hrep
  have hquad : ‖(z : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 = ∫ x, f x ^ 2 := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      norm_sq_eq_integral_sq_of_ae_eq (z : GradientSpace (N := N) ⊤ q).fst hrep'
  have H := hnash z
  nth_rw 1 [hquad] at H
  rw [eLpNorm_congr_ae hrep,
    eLpNorm_one_toReal_eq_integral_of_nonneg (memLp_one_iff_integrable.mp hf₁) hnonneg] at H
  exact H

end HeatKernel.Sobolev

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.FiniteSupportWeakFromNash
public import HeatKernel.Sobolev.ZeroBoundaryRepresentatives
public import HeatKernel.Sobolev.ScaledEnergyTruncation
import Mathlib.Tactic

/-! # Weak power estimates with radius-scaled horizontal energy -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- A radius-scaled Nash estimate gives the weak distribution bound on the zero-boundary domain. -/
theorem measure_abs_gt_le_on_zeroBoundaryGraph_of_scaled_nash {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hfinite : volume (U : Set (Fin N → ℝ)) ≠ ⊤)
    (r : ℝ) {C a b : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hb₁ : b < 1)
    (hnash : ∀ z : zeroBoundaryGraph U X, ∀ f : (Fin N → ℝ) → ℝ,
      Measurable f → (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] f →
      (∀ x, 0 ≤ f x) → (∫ x, f x ^ 2) ≤ C * (r ^ 2 * ‖(z : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(z : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ^ a * (∫ x, f x) ^ b)
    (v : zeroBoundaryGraph U X) {s : ℝ} (hs : 0 < s) :
    volume.real {x | s < |(v : GradientSpace (N := N) ⊤ q).fst x|} ≤
      (2 ^ ((2 - b) / (1 - b)) * (C * (r ^ 2 * ‖(v : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(v : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ^ a)) ^ (1 / (1 - b)) *
        s ^ (-((2 - b) / (1 - b))) := by
  obtain ⟨f, hfm, hsupport, hrep, _⟩ := exists_measurable_supported_zeroBoundaryGraph_rep U X v
  have htrunc (t : ℝ) (ht : 0 < t) :
      (∫ x, levelTruncation f t x ^ 2) ≤
        (C * (r ^ 2 * ‖(v : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(v : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ^ a) * (∫ x, levelTruncation f t x) ^ b := by
    obtain ⟨z, hzrep, he⟩ :=
      exists_zeroBoundaryGraph_levelTruncation_scaled_energy_of_ae_eq U X hX v r hrep ht.le
    have hn := hnash z (levelTruncation f t) (measurable_levelTruncation hfm t) hzrep
      (fun x => (levelTruncation_bounds f ht.le x).1)
    apply hn.trans
    apply mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) he ha) hC)
    exact Real.rpow_nonneg (integral_nonneg (fun x => (levelTruncation_bounds f ht.le x).1)) b
  have H := measure_abs_gt_le_of_supported_truncated_nash hfm hsupport hfinite
    (mul_nonneg hC (Real.rpow_nonneg (by positivity) a)) hb hb₁ htrunc hs
  have hset : {x | s < |(v : GradientSpace (N := N) ⊤ q).fst x|} =ᵐ[volume]
      {x | s < |f x|} := by
    filter_upwards [hrep] with x hx
    simp only [hx]
  change (volume {x | s < |(v : GradientSpace (N := N) ⊤ q).fst x|}).toReal ≤ _
  rw [measure_congr hset]
  exact H

end HeatKernel.Sobolev

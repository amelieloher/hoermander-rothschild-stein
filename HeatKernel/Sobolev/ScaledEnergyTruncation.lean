-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.LevelTruncationForm
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic

/-! # Level truncations and radius-scaled horizontal energy -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- Level truncation decreases the value norm separately from the horizontal energy. -/
theorem exists_zeroBoundaryGraph_levelTruncation_scaled_energy {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (v : zeroBoundaryGraph U X) (r : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ w : zeroBoundaryGraph U X,
      (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        levelTruncation (v : GradientSpace (N := N) ⊤ q).fst t ∧
      r ^ 2 * ‖(w : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(w : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤
      r ^ 2 * ‖(v : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(v : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 := by
  obtain ⟨z, hz, hrep, he, _⟩ := exists_zeroBoundaryGraph_levelTruncation U X hX v ht
  have hzmem : MemLp (z : GradientSpace (N := N) ⊤ q).fst 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp (z : GradientSpace (N := N) ⊤ q).fst
  have hvmem : MemLp (v : GradientSpace (N := N) ⊤ q).fst 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp (v : GradientSpace (N := N) ⊤ q).fst
  have hnorm : ∀ᵐ x ∂volume, ‖(z : GradientSpace (N := N) ⊤ q).fst x‖ ≤
      ‖(v : GradientSpace (N := N) ⊤ q).fst x‖ := by
    filter_upwards [hrep] with x hx
    rw [hx, Real.norm_eq_abs, abs_of_nonneg (levelTruncation_bounds _ ht x).1,
      Real.norm_eq_abs]
    exact (min_le_left _ _).trans (max_le (sub_le_self _ ht) (abs_nonneg _))
  have hval : ‖(z : GradientSpace (N := N) ⊤ q).fst‖ ≤
      ‖(v : GradientSpace (N := N) ⊤ q).fst‖ := by
    have H := ENNReal.toReal_mono hvmem.eLpNorm_ne_top
      (eLpNorm_mono_ae hzmem.aestronglyMeasurable hnorm (p := 2))
    simpa only [Lp.norm_def, Opens.coe_top, Measure.restrict_univ] using H
  have hgrad : ‖(z : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 ≤
      ‖(v : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 := by
    simpa only [horizontalEnergy, energyGradient_apply, real_inner_self_eq_norm_sq] using he
  refine ⟨⟨z, hz⟩, hrep, ?_⟩
  exact add_le_add (mul_le_mul_of_nonneg_left hgrad (sq_nonneg r))
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hval)

/-- The scaled-energy contraction applies to any almost everywhere equal representative. -/
theorem exists_zeroBoundaryGraph_levelTruncation_scaled_energy_of_ae_eq {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (v : zeroBoundaryGraph U X) (r : ℝ) {f : (Fin N → ℝ) → ℝ}
    (hf : (v : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] f) {t : ℝ} (ht : 0 ≤ t) :
    ∃ w : zeroBoundaryGraph U X,
      (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] levelTruncation f t ∧
      r ^ 2 * ‖(w : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(w : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤
      r ^ 2 * ‖(v : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(v : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 := by
  obtain ⟨w, hw, he⟩ := exists_zeroBoundaryGraph_levelTruncation_scaled_energy U X hX v r ht
  refine ⟨w, hw.trans ?_, he⟩
  filter_upwards [hf] with x hx
  simp only [levelTruncation, hx]

end HeatKernel.Sobolev

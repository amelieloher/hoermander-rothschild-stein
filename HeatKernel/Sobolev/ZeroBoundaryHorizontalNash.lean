-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.SmoothHorizontalNash
public import HeatKernel.Sobolev.SmoothGradientMoment
public import HeatKernel.Sobolev.ZeroBoundaryNashClosure
import Mathlib.Tactic
import all HeatKernel.Geometry.CarnotPoint
import all Mathlib.Basic.Real.Basic

/-! # Horizontal Nash inequalities on zero-boundary graph domains -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- Smooth horizontal averaging gives a Nash estimate on every finite-volume zero-boundary domain. -/
theorem norm_sq_le_horizontal_nash_on_zeroBoundaryGraph {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (U : Opens (Fin N → ℝ)) (hfinite : volume (U : Set (Fin N → ℝ)) ≠ ⊤)
    {r ν : ℝ} (hr : 0 < r) (hν : 0 < ν) (hQ : (G.homogeneousDimension : ℝ) ≤ ν)
    (v : zeroBoundaryGraph U (G.horizontalFields hq)) :
    ‖(v : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤
      (((Real.sqrt (576 * (66 : ℝ) ^ G.homogeneousDimension) + 2) ^ 2 *
        2 ^ (ν / (ν + 2))) *
        (Real.sqrt ((volume.real (horizontalBall (G.horizontalFields hq) 0 r))⁻¹)) ^
          (4 / (ν + 2))) *
      (r ^ 2 * ‖(v : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(v : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ^ (ν / (ν + 2)) *
      (eLpNorm (v : GradientSpace (N := N) ⊤ q).fst 1 volume).toReal ^ (4 / (ν + 2)) := by
  let C := (((Real.sqrt (576 * (66 : ℝ) ^ G.homogeneousDimension) + 2) ^ 2 *
    2 ^ (ν / (ν + 2))) *
    (Real.sqrt ((volume.real (horizontalBall (G.horizontalFields hq) 0 r))⁻¹)) ^
      (4 / (ν + 2)))
  have hcore : ∀ w : zeroBoundaryGraph U (G.horizontalFields hq),
      (w : GradientSpace (N := N) ⊤ q) ∈ interiorGradientPairs U (G.horizontalFields hq) →
      ‖(w : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤
        C * (r ^ 2 * ‖(w : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
          1 * ‖(w : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ^ (ν / (ν + 2)) *
        (eLpNorm (w : GradientSpace (N := N) ⊤ q).fst 1 volume).toReal ^ (4 / (ν + 2)) := by
    intro w hwcore
    simp only [one_mul]
    obtain ⟨f, hf, _, _, hrep, hgrad⟩ := hwcore
    have hf₁ : MemLp f 1 volume := (memLp_congr_ae hrep).mp
      (memLp_one_zeroBoundaryGraph U (G.horizontalFields hq) hfinite w).1
    have hf₂ : MemLp f 2 volume := by
      apply (memLp_congr_ae hrep).mp
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        Lp.memLp (w : GradientSpace (N := N) ⊤ q).fst
    have hmoment := lintegral_horizontalGradientNorm_sq_eq_norm_snd
      (G.horizontalFields hq) (w : GradientSpace (N := N) ⊤ q) f hgrad
    have hfin : (∫⁻ x, ENNReal.ofReal
        (horizontalGradientNorm (G.horizontalFields hq) f x ^ 2)) ≠ ⊤ := by
      rw [hmoment]
      exact ENNReal.ofReal_ne_top
    have hn : ‖hf₂.toLp f‖ = ‖(w : GradientSpace (N := N) ⊤ q).fst‖ := by
      rw [Lp.norm_toLp, Lp.norm_def]
      simp only [Opens.coe_top, Measure.restrict_univ]
      rw [eLpNorm_congr_ae hrep]
    have H := CarnotPoint.norm_sq_le_nash_of_contDiff G hq hqpos hspan hw hr hν hQ f
      (hf.of_le (by simp)) hf₁ hf₂ hfin
    have H' : ‖hf₂.toLp f‖ ^ 2 ≤
        ((Real.sqrt (576 * (66 : ℝ) ^ G.homogeneousDimension) + 2) ^ 2 *
          2 ^ (ν / (ν + 2))) *
        (r ^ 2 * (∫⁻ x, ENNReal.ofReal
          (horizontalGradientNorm (G.horizontalFields hq) f x ^ 2)).toReal + ‖hf₂.toLp f‖ ^ 2) ^
          (ν / (ν + 2)) *
        (Real.sqrt ((volume.real (horizontalBall (G.horizontalFields hq) 0 r))⁻¹ *
          (eLpNorm f 1 volume).toReal ^ 2)) ^ (4 / (ν + 2)) := by
      convert H using 1 <;> rfl
    rw [hmoment, ENNReal.toReal_ofReal (sq_nonneg _), hn] at H'
    have hm : Real.sqrt ((volume.real (horizontalBall (G.horizontalFields hq) 0 r))⁻¹ *
        (eLpNorm f 1 volume).toReal ^ 2) =
        Real.sqrt ((volume.real (horizontalBall (G.horizontalFields hq) 0 r))⁻¹) *
          (eLpNorm f 1 volume).toReal := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ENNReal.toReal_nonneg]
    rw [hm, Real.mul_rpow (Real.sqrt_nonneg _) ENNReal.toReal_nonneg,
      ← eLpNorm_congr_ae hrep] at H'
    dsimp only [C]
    convert H' using 1; ring
  have H := norm_sq_le_nash_on_zeroBoundaryGraph_of_core U (G.horizontalFields hq) hfinite
    (by positivity : 0 ≤ ν / (ν + 2)) (by positivity : 0 ≤ 4 / (ν + 2)) hcore v
  simpa only [one_mul, C] using H

end HeatKernel.Sobolev

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSignedMatrixUnitGapBounds
import Mathlib.Tactic

/-! # Essential mean-value bounds on interior unit cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- The positive-power norm steps give a uniform essential quadratic mean-value
bound on every strictly time-truncated interior unit cylinder. The constant is
independent of its terminal time; the outer quadratic norm may be infinite. -/
theorem exists_uniform_signed_matrix_unit_positive_part_terminal_bound {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → (Fin N → ℝ) → ℝ)
      (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ),
      IsLocalWeakSolution G hq hqpos hw hspan
        coeff ⟨Ioo (-1 : ℝ) 0, isOpen_Ioo⟩
        (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1) u →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      ∀ b : ℝ, -1 / 16 ≤ b → b < 0 →
      eLpNormEssSup (fun z : ℝ × (Fin N → ℝ) => max (u z.1 z.2) 0)
        ((volume.restrict (Ioo (-1 / 2 : ℝ) b)).prod (volume.restrict
          (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) (1 / 2) : Set (Fin N → ℝ)))) ≤
        ENNReal.ofReal C * eLpNorm (fun z : ℝ × (Fin N → ℝ) => max (u z.1 z.2) 0) 2
          ((volume.restrict (Ioo (-1 : ℝ) 0)).prod (volume.restrict
            (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1 : Set (Fin N → ℝ)))) := by
  obtain ⟨C, hC, hgap⟩ := exists_uniform_signed_matrix_unit_positive_part_gap_bound G hq hqpos hspan hw hν ell upper hell hupper
  let D := C * (1 / 4 : ℝ) ^ (-(1 + ν / 2))
  have hD : 0 < D := mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨D, hD, ?_⟩
  intro u coeff hu ha hbound b hbLow hbTop
  have hs := hgap u coeff hu ha hbound b hbLow hbTop (1 / 2) (3 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num only [show (3 / 4 : ℝ) - 1 / 2 = 1 / 4 by norm_num] at hs
  simp only [← neg_div] at hs
  have hinner : (volume.restrict (Ioo (-1 / 2 : ℝ) b)).prod
      (volume.restrict (CarnotPoint.coordinateBall G hq hqpos hspan
        (0 : Fin N → ℝ) (1 / 2) : Set (Fin N → ℝ))) ≤
      (volume.restrict (Icc (-1 / 2 : ℝ) b)).prod
        (volume.restrict (CarnotPoint.coordinateBall G hq hqpos hspan
          (0 : Fin N → ℝ) (1 / 2) : Set (Fin N → ℝ))) :=
    Measure.prod_mono (Measure.restrict_mono Ioo_subset_Icc_self le_rfl) le_rfl
  have houter : (volume.restrict (Icc (-3 / 4 : ℝ) b)).prod
      (volume.restrict (CarnotPoint.coordinateBall G hq hqpos hspan
        (0 : Fin N → ℝ) (3 / 4) : Set (Fin N → ℝ))) ≤
      (volume.restrict (Ioo (-1 : ℝ) 0)).prod
        (volume.restrict (CarnotPoint.coordinateBall G hq hqpos hspan
          (0 : Fin N → ℝ) 1 : Set (Fin N → ℝ))) := by
    apply Measure.prod_mono
    · apply Measure.restrict_mono ?_ le_rfl
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    · exact Measure.restrict_mono
        (Metric.ball_subset_ball (α := CarnotPoint G hq hqpos hspan) (by norm_num)) le_rfl
  exact (eLpNormEssSup_mono_measure _ (Measure.absolutelyContinuous_of_le hinner)).trans
    (hs.trans (mul_le_mul' le_rfl (eLpNorm_mono_measure _ houter)))

end HeatKernel

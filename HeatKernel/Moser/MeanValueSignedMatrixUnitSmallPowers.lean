-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSignedMatrixUnitGapBounds
public import HeatKernel.Moser.MeanValueIncreasingRadii
public import HeatKernel.Moser.MeanValueMatrixUnitCompactBounds
public import HeatKernel.Moser.MeanValueSmallPowerNorms
import Mathlib.Tactic

/-! # Elliptic matrix unit mean values below the quadratic exponent -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- Every fixed exponent between zero and two gives a unit-cylinder mean-value
estimate for signed uniformly elliptic matrix weak solutions. The
constant is uniform in the strictly interior terminal time, with no additional
boundedness or quadratic-integrability hypothesis on the solution. -/
theorem exists_uniform_signed_matrix_unit_small_power_terminal_bound {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν p : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν)
    (hp : 0 < p) (hp2 : p < 2)
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
      eLpNormEssSup (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2)
        ((volume.restrict (Ioo (-1 / 2 : ℝ) b)).prod (volume.restrict
          (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) (1 / 2) : Set (Fin N → ℝ)))) ≤
        ENNReal.ofReal C * eLpNorm (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) (ENNReal.ofReal p)
          ((volume.restrict (Ioo (-1 : ℝ) 0)).prod (volume.restrict
            (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1 : Set (Fin N → ℝ)))) := by
  obtain ⟨C, hC, hgap⟩ := exists_uniform_signed_matrix_unit_gap_essential_bound G hq hqpos hspan hw hν ell upper hell hupper
  let κ := 1 + ν / 2
  let B := (2 : ℝ) ^ κ
  let F := C * (1 / 4 : ℝ) ^ (-κ) * B
  have hν2 : 2 < ν := lt_of_le_of_lt (le_max_left _ _) hν
  have hB : 1 ≤ B := Real.one_le_rpow (by norm_num) (by dsimp only [κ]; linarith)
  have hF : 0 < F := mul_pos
    (mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _))
    (Real.rpow_pos_of_pos (by norm_num) _)
  obtain ⟨D, hD, hiteration⟩ := exists_small_power_constant_of_quadratic_iteration
    (α := ℝ × (Fin N → ℝ)) hp hp2 hF hB
  refine ⟨D, hD, ?_⟩
  intro u coeff hu ha hbound b hbLow hbTop
  let f := fun z : ℝ × (Fin N → ℝ) => u z.1 z.2
  let radii := increasingCutoffRadius (1 / 2) (3 / 4)
  let μ := fun r : ℝ => (volume.restrict (Icc (-r) b)).prod
    (volume.restrict (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) r : Set (Fin N → ℝ)))
  let μunit := (volume.restrict (Ioo (-1 : ℝ) 0)).prod
    (volume.restrict (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1 : Set (Fin N → ℝ)))
  have hrange (j : ℕ) : radii j ∈ Icc (1 / 2 : ℝ) (3 / 4) := by
    have h := increasingCutoffRadius_mem_Ico (by norm_num : (1 / 2 : ℝ) < 3 / 4) j
    exact ⟨h.1, h.2.le⟩
  have hμ (j : ℕ) : μ (radii j) ≤ μunit := by
    apply Measure.prod_mono
    · apply Measure.restrict_mono ?_ le_rfl
      intro t ht
      constructor <;> linarith [(hrange j).2, ht.1, ht.2]
    · exact Measure.restrict_mono
        (Metric.ball_subset_ball (α := CarnotPoint G hq hqpos hspan)
          (show radii j ≤ 1 by linarith [(hrange j).2])) le_rfl
  have hf (j : ℕ) : AEStronglyMeasurable f (μ (radii j)) :=
    hu.aestronglyMeasurable_unit_inner_product_cylinder G hq hqpos hspan hw (fun t ht => by
      constructor <;> linarith [(hrange j).2, ht.1, ht.2]) (by linarith [(hrange j).2])
  obtain ⟨H, hH⟩ := exists_signed_matrix_unit_interior_uniform_essential_bound G hq hqpos hspan hw ell upper hell hupper hu ha hbound hbLow hbTop
  have hquad (j : ℕ) : eLpNormEssSup f (μ (radii j)) ≤
      ENNReal.ofReal (F * B ^ j) * eLpNorm f 2 (μ (radii (j + 1))) := by
    have hs := hgap u coeff hu ha hbound b hbLow hbTop (radii j) (radii (j + 1))
      ⟨(hrange j).1, by linarith [(hrange j).2]⟩
      ⟨(hrange (j + 1)).1, by linarith [(hrange (j + 1)).2]⟩ (increasingCutoffRadius_lt_succ (by norm_num) j)
    have hcoef : C * (radii (j + 1) - radii j) ^ (-(1 + ν / 2)) = F * B ^ j := by
      change C * (increasingCutoffRadius (1 / 2) (3 / 4) (j + 1) -
        increasingCutoffRadius (1 / 2) (3 / 4) j) ^ (-κ) = _
      rw [increasingCutoffRadius_gap_rpow_neg (by norm_num : (1 / 2 : ℝ) < 3 / 4) κ j]
      norm_num only [show (3 / 4 : ℝ) - 1 / 2 = 1 / 4 by norm_num]
      dsimp only [F, B]
      rw [pow_succ]
      ring
    rw [hcoef] at hs
    exact hs
  have hs := hiteration μunit (fun j => μ (radii j)) f hμ hf
    ⟨H, fun j => hH (radii j) (hrange j)⟩ hquad
  simp only [radii, increasingCutoffRadius_zero] at hs
  have hinner : (volume.restrict (Ioo (-(1 / 2 : ℝ)) b)).prod
      (volume.restrict (CarnotPoint.coordinateBall G hq hqpos hspan
        (0 : Fin N → ℝ) (1 / 2) : Set (Fin N → ℝ))) ≤ μ (1 / 2) :=
    Measure.prod_mono (Measure.restrict_mono Ioo_subset_Icc_self le_rfl) le_rfl
  simpa only [← neg_div] using
    (eLpNormEssSup_mono_measure f (Measure.absolutelyContinuous_of_le hinner)).trans hs

end HeatKernel

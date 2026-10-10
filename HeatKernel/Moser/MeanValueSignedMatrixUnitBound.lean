-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSignedMatrixUnitEssentialBound
public import HeatKernel.Moser.MeanValueTerminalExhaustion
public import HeatKernel.Moser.WeakSolutionScaling
public import HeatKernel.Moser.MeanValueSignedParts
import Mathlib.Tactic

/-! # Uniform quadratic mean values for signed matrix weak solutions -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- Compact terminal cylinders have a signed quadratic mean-value bound, uniform in the top time. -/
theorem exists_uniform_signed_matrix_unit_terminal_bound {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → (Fin N → ℝ) → ℝ)
      (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ),
      IsLocalWeakSolution G hq hqpos hw hspan coeff ⟨Ioo (-1 : ℝ) 0, isOpen_Ioo⟩
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
        ENNReal.ofReal C * eLpNorm (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) 2
          ((volume.restrict (Ioo (-1 : ℝ) 0)).prod (volume.restrict
            (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1 : Set (Fin N → ℝ)))) := by
  obtain ⟨C, hC, hpart⟩ := exists_uniform_signed_matrix_unit_positive_part_terminal_bound
    G hq hqpos hspan hw hν ell upper hell hupper
  refine ⟨C, hC, ?_⟩
  intro u coeff hu ha hbound b hbLow hbTop
  let μ := (volume.restrict (Ioo (-1 : ℝ) 0)).prod (volume.restrict
    (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1 : Set (Fin N → ℝ)))
  have hm : AEStronglyMeasurable (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) μ := by
    dsimp only [μ]
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hu.1
  have hp := hpart u coeff hu ha hbound b hbLow hbTop
  have hnweak : IsLocalWeakSolution G hq hqpos hw hspan coeff
      ⟨Ioo (-1 : ℝ) 0, isOpen_Ioo⟩
      (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1)
      (fun t x => -u t x) := by
    simpa only [neg_one_mul] using
      IsLocalWeakSolution.const_mul G hq hqpos hw hspan hu (-1)
  have hn := hpart (fun t x => -u t x) coeff hnweak ha hbound b hbLow hbTop
  exact eLpNormEssSup_le_mul_eLpNorm_of_positive_negative_parts hm hp hn

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSignedMatrixUnitSmallPowers
public import HeatKernel.Moser.MeanValueTerminalExhaustion
public import HeatKernel.Moser.MeanValueSignedMatrixUnitBound
public import HeatKernel.Moser.MeanValueHigherPowers
import Mathlib.Tactic

/-! # Elliptic matrix unit mean values at every positive exponent -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- Every fixed positive exponent gives a terminal unit mean-value bound, uniform
in the strictly interior terminal time. Constants may depend on the exponent. -/
theorem exists_uniform_signed_matrix_unit_positive_power_terminal_bound {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν p : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν) (hp : 0 < p)
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
  by_cases hp2 : p < 2
  · exact exists_uniform_signed_matrix_unit_small_power_terminal_bound G hq hqpos hspan hw hν hp hp2 ell upper hell hupper
  have h2p : 2 ≤ p := le_of_not_gt hp2
  let μunit := (volume.restrict (Ioo (-1 : ℝ) 0)).prod
    (volume.restrict (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1 : Set (Fin N → ℝ)))
  have hfinite : μunit univ ≠ ⊤ := by
    dsimp only [μunit]
    rw [← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
      Measure.restrict_apply_univ]
    apply ENNReal.mul_ne_top
    · rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    · rw [CarnotPoint.coordinateBall_eq_horizontalBall]
      exact (volume_horizontalBall_lt_top G hq hqpos hspan hw (0 : Fin N → ℝ) (by norm_num)).ne
  obtain ⟨A, hA, hquadratic⟩ :=
    exists_uniform_signed_matrix_unit_terminal_bound G hq hqpos hspan hw hν ell upper hell hupper
  obtain ⟨C, hC, hhigher⟩ := exists_higher_power_constant_of_quadratic_bound μunit hfinite h2p hA
  refine ⟨C, hC, ?_⟩
  intro u coeff hu ha hbound b hbLow hbTop
  let f := fun z : ℝ × (Fin N → ℝ) => u z.1 z.2
  have hf : AEStronglyMeasurable f μunit := by
    dsimp only [μunit]
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hu.1
  exact hhigher _ f hf (hquadratic u coeff hu ha hbound b hbLow hbTop)

/-- Signed solutions of a uniformly elliptic matrix weak equation satisfy the
unit essential mean-value estimate for every fixed positive exponent, including
cylinders touching the open top time. No terminal trace or outer quadratic norm
is required. The constant may depend on the exponent. -/
theorem exists_uniform_signed_matrix_unit_positive_power_bound {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν p : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν) (hp : 0 < p)
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
      eLpNormEssSup (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2)
        ((volume.restrict (Ioo (-1 / 2 : ℝ) 0)).prod (volume.restrict
          (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) (1 / 2) : Set (Fin N → ℝ)))) ≤
        ENNReal.ofReal C * eLpNorm (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) (ENNReal.ofReal p)
          ((volume.restrict (Ioo (-1 : ℝ) 0)).prod (volume.restrict
            (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1 : Set (Fin N → ℝ)))) := by
  obtain ⟨C, hC, hterminal⟩ :=
    exists_uniform_signed_matrix_unit_positive_power_terminal_bound G hq hqpos hspan hw hν hp ell upper hell hupper
  refine ⟨C, hC, ?_⟩
  intro u coeff hu ha hbound
  let f := fun z : ℝ × (Fin N → ℝ) => u z.1 z.2
  let B : Set (Fin N → ℝ) :=
    CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) (1 / 2)
  let μunit := (volume.restrict (Ioo (-1 : ℝ) 0)).prod (volume.restrict
    (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1 : Set (Fin N → ℝ)))
  change eLpNormEssSup f ((volume.restrict (Ioo (-1 / 2 : ℝ) 0)).prod
    (volume.restrict B)) ≤ ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) μunit
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  apply eLpNormEssSup_prod_Ioo_le_of_uniform_terminal_bounds volume f
    (c := -1 / 16) (by norm_num) B
  intro b hbLow hbTop
  have hb := hterminal u coeff hu ha hbound b hbLow hbTop
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hb
  exact hb

end HeatKernel

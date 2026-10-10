-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CoefficientEnergy
public import HeatKernel.Form.EnergyDensity
import Mathlib.Tactic.Linter

/-! # Indicator-weighted horizontal energy forms -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace HeatKernel

/-- The identity matrix weighted by the indicator of a spatial set. -/
def indicatorMatrix {N q : ℕ} (s : Set (Fin N → ℝ)) (i j : Fin q) (x : Fin N → ℝ) : ℝ :=
  s.indicator (fun _ => if i = j then 1 else 0) x

/-- Measurable sets give measurable indicator matrix entries. -/
theorem aestronglyMeasurable_indicatorMatrix {N q : ℕ} {s : Set (Fin N → ℝ)}
    (hs : MeasurableSet s) (i j : Fin q) : AEStronglyMeasurable (indicatorMatrix s i j) volume :=
  (stronglyMeasurable_const.indicator hs).aestronglyMeasurable

/-- Indicator matrices are symmetric. -/
theorem indicatorMatrix_symm {N q : ℕ} (s : Set (Fin N → ℝ)) (x : Fin N → ℝ) (i j : Fin q) :
    indicatorMatrix s i j x = indicatorMatrix s j i x := by
  simp only [indicatorMatrix, eq_comm]

/-- The quadratic expression is the squared coordinate norm on the indicated set and zero off it. -/
theorem matrixEnergy_indicatorMatrix {N q : ℕ} (s : Set (Fin N → ℝ)) (x : Fin N → ℝ)
    (ξ : Fin q → ℝ) : matrixEnergy (fun i j => indicatorMatrix s i j x) ξ = s.indicator (fun _ => coordinateNormSq ξ) x := by
  classical
  by_cases hx : x ∈ s
  · simp [indicatorMatrix, hx, matrixEnergy, coordinateNormSq, pow_two]
  · simp [indicatorMatrix, hx, matrixEnergy]

/-- Indicator matrices are positive and bounded above by the identity quadratic form. -/
theorem matrixEnergy_indicatorMatrix_bounds {N q : ℕ} (s : Set (Fin N → ℝ)) (x : Fin N → ℝ)
    (ξ : Fin q → ℝ) :
    0 * coordinateNormSq ξ ≤ matrixEnergy (fun i j => indicatorMatrix s i j x) ξ ∧
      matrixEnergy (fun i j => indicatorMatrix s i j x) ξ ≤ 1 * coordinateNormSq ξ := by
  rw [matrixEnergy_indicatorMatrix]
  by_cases hx : x ∈ s
  · simp only [indicator_of_mem hx, zero_mul, one_mul]
    exact ⟨Finset.sum_nonneg fun _ _ => sq_nonneg _, le_rfl⟩
  · simp only [indicator_of_notMem hx, zero_mul, one_mul]
    exact ⟨le_rfl, Finset.sum_nonneg fun _ _ => sq_nonneg _⟩

/-- Indicator-weighted coefficient forms are set integrals of the horizontal energy density. -/
theorem coefficientEnergy_indicatorMatrix {N q : ℕ} (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    {s : Set (Fin N → ℝ)} (hs : MeasurableSet s) (u v : energyGraph (N := N) ⊤ X) :
    coefficientEnergy ⊤ X (indicatorMatrix s) u v =
      ∫ x in s, horizontalEnergyDensity ⊤ X u v x := by
  classical
  simp only [coefficientEnergy, Opens.coe_top, Measure.restrict_univ]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ s
    · simp [coefficientEnergyDensity, indicatorMatrix, horizontalEnergyDensity, hx]
    · simp [coefficientEnergyDensity, indicatorMatrix, hx]


end HeatKernel

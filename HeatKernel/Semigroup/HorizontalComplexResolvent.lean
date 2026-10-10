-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.HorizontalHeatOperators

/-! # Complexification and spectral bounds of the horizontal form resolvent -/

@[expose] public section
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped NNReal
namespace HeatKernel
variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

theorem horizontalFormResolvent_complex_isPositive :
    (complexL2Extension (volume.restrict (U : Set (Fin N → ℝ)))
      (horizontalFormResolvent U X)).IsPositive :=
  complexL2Extension_isPositive _ _ (horizontalFormResolvent_isPositive U X)

theorem horizontalFormResolvent_complex_isSelfAdjoint :
    IsSelfAdjoint (complexL2Extension (volume.restrict (U : Set (Fin N → ℝ)))
      (horizontalFormResolvent U X)) :=
  (horizontalFormResolvent_complex_isPositive U X).isSelfAdjoint

theorem norm_horizontalFormResolvent_complex_le_one :
    ‖complexL2Extension (volume.restrict (U : Set (Fin N → ℝ)))
      (horizontalFormResolvent U X)‖ ≤ 1 :=
  norm_complexL2Extension_le_one _ _ (norm_horizontalFormResolvent_le_one U X)

theorem spectrum_horizontalFormResolvent_complex_subset :
    spectrum ℝ (complexL2Extension (volume.restrict (U : Set (Fin N → ℝ)))
      (horizontalFormResolvent U X)) ⊆ Icc (0 : ℝ) 1 :=
  spectrum_subset_Icc_of_isPositive_norm_le_one _
    (horizontalFormResolvent_complex_isPositive U X)
    (norm_horizontalFormResolvent_complex_le_one U X)

end HeatKernel

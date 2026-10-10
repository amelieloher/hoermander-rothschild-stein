-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiMeasureNormalization
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic

/-! # Nonnegative functions in the normalized moment convention -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- On a nonnegative function the essential norm supremum is exactly the
essential supremum of its nonnegative extended-real representative. -/
theorem essSup_ofReal_eq_eLpNormEssSup_of_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : α → ℝ}
    (hu : ∀ᵐ y ∂μ, 0 ≤ u y) :
    essSup (fun y => ENNReal.ofReal (u y)) μ = eLpNormEssSup u μ := by
  apply essSup_congr_ae
  exact hu.mono fun _ hy => (Real.enorm_eq_ofReal hy).symm

/-- The norm on a restriction scaled by its inverse mass is the corresponding
normalized positive moment. No finiteness of the moment is assumed. -/
theorem eLpNorm_normalized_restrict_eq_moment_of_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {V : Set α}
    {u : α → ℝ} {p : ℝ} (hp : 0 < p)
    (hu : AEStronglyMeasurable u (μ.restrict V))
    (hn : ∀ᵐ y ∂μ.restrict V, 0 ≤ u y) :
    eLpNorm u (ENNReal.ofReal p) ((μ V)⁻¹ • μ.restrict V) =
      ((μ V)⁻¹ * (∫⁻ y in V, ENNReal.ofReal (u y) ^ p ∂μ)) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top (hu.smul_measure _), ENNReal.toReal_ofReal hp.le,
    lintegral_smul_measure, smul_eq_mul]
  congr 1
  congr 1
  apply lintegral_congr_ae
  exact hn.mono fun _ hy => congrArg (fun v : ℝ≥0∞ => v ^ p) (Real.enorm_eq_ofReal hy)

end HeatKernel

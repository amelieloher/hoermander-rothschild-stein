-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.TotalCoefficientSlices
import Mathlib.Tactic.Linter

/-! # Everywhere defined bounded measurable coefficient slices -/

@[expose] public section

noncomputable section

open MeasureTheory Filter

namespace HeatKernel

/-- A bounded jointly measurable matrix field has a version with bounded measurable spatial
slices at every time. The version agrees at almost every time at every spatial point. -/
theorem exists_bounded_measurable_total_slices {T E : Type*}
    [MeasurableSpace T] [MeasurableSpace E] {μ : Measure T} {ν : Measure E} [SFinite ν] {q : ℕ}
    (a : Fin q → Fin q → T × E → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) (μ.prod ν))
    (hb : ∀ i j, ∀ᵐ z ∂μ.prod ν, ‖a i j z‖ ≤ C) :
    ∃ a' : Fin q → Fin q → T × E → ℝ,
      (∀ i j, AEStronglyMeasurable (a' i j) (μ.prod ν)) ∧
      (∀ t i j, AEStronglyMeasurable (fun x => a' i j (t, x)) ν ∧
        ∀ᵐ x ∂ν, ‖a' i j (t, x)‖ ≤ C) ∧
      ∀ᵐ t ∂μ, ∀ i j x, a' i j (t, x) = a i j (t, x) := by
  let P : (Fin q → Fin q → E → ℝ) → Prop := fun b =>
    ∀ i j, AEStronglyMeasurable (b i j) ν ∧ ∀ᵐ x ∂ν, ‖b i j x‖ ≤ C
  have hP : ∀ᵐ t ∂μ, P (fun i j x => a i j (t, x)) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    filter_upwards [(ha i j).prodMk_left, Measure.ae_ae_of_ae_prod (hb i j)] with t ht hs
    exact ⟨ht, hs⟩
  have hPzero : P (fun _ _ _ => 0) := fun _ _ =>
    ⟨aestronglyMeasurable_const, .of_forall fun _ => by simpa only [norm_zero] using hC⟩
  exact exists_total_coefficient_slices a (fun _ _ _ => 0) ha
    (fun _ _ => aestronglyMeasurable_const) P hPzero hP



end HeatKernel

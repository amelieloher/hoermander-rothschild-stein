-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CoefficientEnergy
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linter

/-! # Measurable completion of exceptional coefficient slices -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter

namespace HeatKernel

/-- Replace exceptional times by one valid measurable coefficient field. The resulting field
is jointly measurable, satisfies the slice property at every time, and agrees with the original
field at almost every time simultaneously at every spatial point. -/
theorem exists_total_coefficient_slices {T E : Type*} [MeasurableSpace T] [MeasurableSpace E]
    {μ : Measure T} {ν : Measure E} [SFinite ν] {q : ℕ}
    (a : Fin q → Fin q → T × E → ℝ) (b : Fin q → Fin q → E → ℝ)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) (μ.prod ν))
    (hb : ∀ i j, AEStronglyMeasurable (b i j) ν)
    (P : (Fin q → Fin q → E → ℝ) → Prop) (hPb : P b)
    (hPa : ∀ᵐ t ∂μ, P (fun i j x => a i j (t, x))) :
    ∃ a' : Fin q → Fin q → T × E → ℝ,
      (∀ i j, AEStronglyMeasurable (a' i j) (μ.prod ν)) ∧
      (∀ t, P (fun i j x => a' i j (t, x))) ∧
      ∀ᵐ t ∂μ, ∀ i j x, a' i j (t, x) = a i j (t, x) := by
  classical
  let M := toMeasurable μ {t | ¬ P (fun i j x => a i j (t, x))}
  have hM : MeasurableSet M := measurableSet_toMeasurable _ _
  have hM0 : μ M = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.mp hPa
  have hgood : ∀ᵐ t ∂μ, t ∉ M := by
    apply ae_iff.mpr
    have hs : {t | ¬ t ∉ M} = M := by
      ext t
      exact not_not
    rw [hs]
    exact hM0
  let a' : Fin q → Fin q → T × E → ℝ := fun i j p => if p.1 ∈ M then b i j p.2 else a i j p
  refine ⟨a', ?_, ?_, ?_⟩
  · intro i j
    change AEStronglyMeasurable ((Prod.fst ⁻¹' M).piecewise (fun p : T × E => b i j p.2) (a i j)) (μ.prod ν)
    exact AEStronglyMeasurable.piecewise (hM.preimage measurable_fst)
      (hb i j).comp_snd.restrict (ha i j).restrict
  · intro t
    by_cases ht : t ∈ M
    · simpa [a', ht] using hPb
    · have htP : P (fun i j x => a i j (t, x)) := by
        by_contra hn
        exact ht (subset_toMeasurable μ _ hn)
      simpa [a', ht] using htP
  · filter_upwards [hgood] with t ht i j x
    simp [a', ht]

end HeatKernel

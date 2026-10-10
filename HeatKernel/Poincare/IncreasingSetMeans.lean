-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Continuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace HeatKernel

/-- Means on increasing measurable sets converge to the mean on their finite positive
measure union. -/
theorem tendsto_average_on_increasing_sets
    {A : Type*} [MeasurableSpace A] {μ : Measure A} {s : ℕ → Set A} {S : Set A}
    (hs : ∀ n, MeasurableSet (s n)) (hmono : Monotone s) (hunion : (⋃ n, s n) = S)
    (hfinite : μ S ≠ ⊤) (hpos : μ S ≠ 0) {f : A → ℝ} (hf : IntegrableOn f S μ) :
    Tendsto (fun n => ⨍ x in s n, f x ∂μ) atTop (𝓝 (⨍ x in S, f x ∂μ)) := by
  have hfi : IntegrableOn f (⋃ n, s n) μ := by rwa [hunion]
  have hI : Tendsto (fun n => ∫ x in s n, f x ∂μ) atTop (𝓝 (∫ x in S, f x ∂μ)) := by
    simpa only [hunion] using tendsto_setIntegral_of_monotone hs hmono hfi
  have hM : Tendsto (fun n => μ (s n)) atTop (𝓝 (μ S)) := by
    simpa only [Function.comp_def, hunion] using tendsto_measure_iUnion_atTop (μ := μ) hmono
  have hMR : Tendsto (fun n => μ.real (s n)) atTop (𝓝 (μ.real S)) := by
    simpa only [Function.comp_def, measureReal_def] using (ENNReal.tendsto_toReal hfinite).comp hM
  have h0 : μ.real S ≠ 0 := (ENNReal.toReal_pos hpos hfinite).ne'
  simpa only [setAverage_eq, smul_eq_mul] using (hMR.inv₀ h0).mul hI

end HeatKernel

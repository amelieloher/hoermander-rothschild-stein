-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.NestedMeans
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Squared oscillation about averages of nested sets -/

@[expose] public section
open MeasureTheory Set
namespace HeatKernel.Sobolev

/-- Replacing the mean on a set by the mean on a nested subset costs one plus the
ratio of their volumes. -/
theorem integral_sub_nested_setAverage_sq_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {U V : Set α} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUV : U ⊆ V) (hVfinite : μ V ≠ ⊤) (hUpos : 0 < μ.real U)
    {u : α → ℝ} (hu : IntegrableOn u V μ)
    (hu₂ : IntegrableOn (fun x => u x ^ 2) V μ) :
    (∫ x in V, (u x - (∫ y in U, u y ∂μ) / μ.real U) ^ 2 ∂μ) ≤
      (1 + μ.real V / μ.real U) *
        ∫ x in V, (u x - (∫ y in V, u y ∂μ) / μ.real V) ^ 2 ∂μ := by
  have hind (S : Set α) (f : α → ℝ) :
      (fun x => S.indicator (fun _ => (1 : ℝ)) x * f x) = S.indicator f := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  have havg (S : Set α) (hS : MeasurableSet S) :
      weightedMean μ (S.indicator (fun _ => (1 : ℝ))) u = (∫ x in S, u x ∂μ) / μ.real S := by
    unfold weightedMean
    rw [hind S u, integral_indicator hS, integral_indicator hS, setIntegral_const]
    simp only [smul_eq_mul, mul_one]
  have hconst : IntegrableOn (fun _ : α => (1 : ℝ)) V μ := integrableOn_const hVfinite
  have hv : Integrable (U.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_indicator_iff hU).mpr (hconst.mono_set hUV)
  have hw : Integrable (V.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_indicator_iff hV).mpr hconst
  have hvu : Integrable (fun x => U.indicator (fun _ => (1 : ℝ)) x * u x) μ := by
    simpa only [← indicator_mul_left, one_mul] using
      (integrable_indicator_iff hU).mpr (hu.mono_set hUV)
  have hwu : Integrable (fun x => V.indicator (fun _ => (1 : ℝ)) x * u x) μ := by
    simpa only [← indicator_mul_left, one_mul] using (integrable_indicator_iff hV).mpr hu
  have hvu₂ : Integrable (fun x => U.indicator (fun _ => (1 : ℝ)) x * u x ^ 2) μ := by
    rw [hind U (fun x => u x ^ 2)]
    exact (integrable_indicator_iff hU).mpr (hu₂.mono_set hUV)
  have hwu₂ : Integrable (fun x => V.indicator (fun _ => (1 : ℝ)) x * u x ^ 2) μ := by
    rw [hind V (fun x => u x ^ 2)]
    exact (integrable_indicator_iff hV).mpr hu₂
  have hv₀ : 0 ≤ᵐ[μ] U.indicator (fun _ => (1 : ℝ)) :=
    Filter.Eventually.of_forall (fun x => by by_cases hx : x ∈ U <;> simp [hx])
  have hvw : U.indicator (fun _ => (1 : ℝ)) ≤ᵐ[μ] V.indicator (fun _ => (1 : ℝ)) :=
    Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ U
      · simp [hx, hUV hx]
      · by_cases hy : x ∈ V <;> simp [hx, hy])
  have hmass : 0 < ∫ x, U.indicator (fun _ => (1 : ℝ)) x ∂μ := by
    simpa only [integral_indicator hU, setIntegral_const, smul_eq_mul, mul_one] using hUpos
  have h := integral_weight_mul_sub_nested_weightedMean_sq_le hv hw hvu hwu hvu₂ hwu₂ hv₀ hvw hmass
  rw [havg U hU, havg V hV,
    hind V (fun x => (u x - (∫ y in U, u y ∂μ) / μ.real U) ^ 2),
    hind V (fun x => (u x - (∫ y in V, u y ∂μ) / μ.real V) ^ 2)] at h
  simpa only [integral_indicator hV, integral_indicator hU, setIntegral_const,
    smul_eq_mul, mul_one] using h

end HeatKernel.Sobolev

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicWeakTailIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Spacetime tail measures as integrals of spatial tail measures -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- On finite time and spatial measure spaces, the real measure of a measurable
spacetime tail is the integral of its spatial section measures. -/
theorem measureReal_spacetime_eq_integral_sections {T X : Type*}
    [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A : Set (T × X)} (hA : MeasurableSet A) :
    (μ.prod ν).real A = ∫ t, ν.real (Prod.mk t ⁻¹' A) ∂μ := by
  have hi : Integrable (A.indicator (fun _ : T × X => (1 : ℝ))) (μ.prod ν) :=
    (integrable_const 1).indicator hA
  calc
    (μ.prod ν).real A = ∫ p, A.indicator (fun _ => (1 : ℝ)) p ∂μ.prod ν :=
      (integral_indicator_one hA).symm
    _ = ∫ t, ∫ x, A.indicator (fun _ => (1 : ℝ)) (t, x) ∂ν ∂μ :=
      integral_prod _ hi
    _ = ∫ t, ν.real (Prod.mk t ⁻¹' A) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t =>
        integral_indicator_one (hA.preimage measurable_prodMk_left)

/-- Spatial section measures of a measurable tail are integrable on every compact
time interval when the spatial measure is finite. -/
theorem intervalIntegrable_measureReal_sections {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] {A : Set (ℝ × X)} (hA : MeasurableSet A)
    {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun t => ν.real (Prod.mk t ⁻¹' A)) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  have hi : Integrable (A.indicator (fun _ : ℝ × X => (1 : ℝ)))
      ((volume.restrict (Ioc a b)).prod ν) := (integrable_const 1).indicator hA
  have hs : (fun t => ∫ x, A.indicator (fun _ => (1 : ℝ)) (t, x) ∂ν) =
      (fun t => ν.real (Prod.mk t ⁻¹' A)) := by
    funext t
    exact integral_indicator_one (hA.preimage measurable_prodMk_left)
  simpa only [hs, IntegrableOn] using hi.integral_prod_left

/-- A measurable spacetime tail has inverse-level measure decay whenever its
spatial sections satisfy the quadratic majorant controlled by a signed mean deviation. -/
theorem measureReal_spacetime_tail_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] {A : Set (ℝ × X)} (hA : MeasurableSet A)
    {q E : ℝ → ℝ} {a b ℓ K σ : ℝ}
    (hab : a ≤ b) (hℓ : 0 < ℓ) (hK : 0 ≤ K) (hσ : |σ| ≤ 1)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hn : ∀ t ∈ uIcc a b, 0 ≤ q t)
    (hE : IntervalIntegrable E volume a b)
    (he : ∀ᵐ t ∂volume, t ∈ uIcc a b → E t ≤ 2 * σ * deriv q t)
    (hb : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      ν.real (Prod.mk t ⁻¹' A) ≤ K * (E t / (ℓ / 2 + q t)^2)) :
    ((volume.restrict (Ioc a b)).prod ν).real A ≤ 4 * K / ℓ := by
  rw [measureReal_spacetime_eq_integral_sections (volume.restrict (Ioc a b)) ν hA]
  rw [← intervalIntegral.integral_of_le hab]
  exact integral_logarithmic_tail_majorant_le hab hℓ hK hσ hq hn hE
    (intervalIntegrable_measureReal_sections ν hA hab) he hb

end HeatKernel

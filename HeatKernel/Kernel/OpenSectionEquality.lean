-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Prod

/-! # Equality of continuous sections on open product domains

Almost-everywhere equality on an open first-factor domain upgrades to pointwise
equality when both functions have continuous sections in each factor.
-/

@[expose] public section

open MeasureTheory

namespace HeatKernel

/-- Separate continuity upgrades product almost-everywhere equality on an open domain. -/
theorem eqOn_of_ae_eq_of_continuous_sections_on_open {X Y Z : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [TopologicalSpace Z] [T2Space Z]
    (μ : Measure X) (ν : Measure Y) [μ.IsOpenPosMeasure] [ν.IsOpenPosMeasure] [SFinite ν]
    {U : Set X} (hU : IsOpen U) {f g : X × Y → Z}
    (hfg : f =ᵐ[(μ.restrict U).prod ν] g)
    (hf₁ : ∀ y, ContinuousOn (fun x => f (x, y)) U)
    (hf₂ : ∀ x ∈ U, Continuous (fun y => f (x, y)))
    (hg₁ : ∀ y, ContinuousOn (fun x => g (x, y)) U)
    (hg₂ : ∀ x ∈ U, Continuous (fun y => g (x, y))) :
    Set.EqOn f g (U ×ˢ Set.univ) := by
  have hsections : ∀ᵐ x ∂μ.restrict U, ∀ y, f (x, y) = g (x, y) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hfg, ae_restrict_mem hU.measurableSet] with x hx hxU
    exact fun y => congrFun (Measure.eq_of_ae_eq hx (hf₂ x hxU) (hg₂ x hxU)) y
  intro p hp
  have heq := Measure.eqOn_open_of_ae_eq (hsections.mono fun x hx => hx p.2)
    hU (hf₁ p.2) (hg₁ p.2)
  exact heq hp.1

/-- A continuous product representative agrees everywhere with continuous sections on an open domain. -/
theorem eqOn_continuous_of_ae_eq_of_continuous_sections_on_open {X Y Z : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [TopologicalSpace Z] [T2Space Z]
    (μ : Measure X) (ν : Measure Y) [μ.IsOpenPosMeasure] [ν.IsOpenPosMeasure] [SFinite ν]
    {U : Set X} (hU : IsOpen U) {f g : X × Y → Z}
    (hfg : f =ᵐ[(μ.restrict U).prod ν] g)
    (hf₁ : ∀ y, ContinuousOn (fun x => f (x, y)) U)
    (hf₂ : ∀ x ∈ U, Continuous (fun y => f (x, y)))
    (hg : ContinuousOn g (U ×ˢ Set.univ)) : Set.EqOn f g (U ×ˢ Set.univ) := by
  apply eqOn_of_ae_eq_of_continuous_sections_on_open μ ν hU hfg hf₁ hf₂
  · intro y
    exact hg.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun x hx => ⟨hx, Set.mem_univ y⟩)
  · intro x hx
    exact continuousOn_univ.mp (hg.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun y _ => ⟨hx, Set.mem_univ y⟩))

end HeatKernel

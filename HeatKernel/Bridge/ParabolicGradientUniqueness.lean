-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.ParabolicGradientMeasurability
public import HeatKernel.Bridge.JointAlmostEverywhereEquality
public import RothschildStein.S.WeakDeriv
import Mathlib.Tactic.Linter

/-! # Product-measure uniqueness of local parabolic weak gradients -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Two local square-integrable weak gradients of the same function agree jointly
almost everywhere on the whole open cylinder. No ellipticity hypothesis is needed. -/
theorem ae_eq_parabolic_weak_gradients {N q : ℕ}
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (u : ℝ → (Fin N → ℝ) → ℝ) (g h : Fin q → ℝ → (Fin N → ℝ) → ℝ)
    (hg : ∀ᵐ t ∂volume.restrict (I : Set ℝ), ∀ i, hasWeakWordDeriv X U [i] (u t) (g i t))
    (hh : ∀ᵐ t ∂volume.restrict (I : Set ℝ), ∀ i, hasWeakWordDeriv X U [i] (u t) (h i t))
    (hgb : HasLocalParabolicEnergyBounds I U u g)
    (hhb : HasLocalParabolicEnergyBounds I U u h) (i : Fin q) :
    (fun z : ℝ × (Fin N → ℝ) => g i z.1 z.2) =ᵐ[
      volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))]
      (fun z => h i z.1 z.2) := by
  have hgm := (hgb.aestronglyMeasurable_gradient i).aemeasurable
  have hhm := (hhb.aestronglyMeasurable_gradient i).aemeasurable
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hgm hhm ⊢
  apply ae_eq_of_jointly_aemeasurable_of_ae_slice_eq hgm hhm
  filter_upwards [hg, hh] with t hgt hht
  exact S.hasWeakWordDeriv_unique X U (hgt i) (hht i)

end HeatKernel

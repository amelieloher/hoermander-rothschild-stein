-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LevelSetGradient
import Mathlib.Tactic.Linter

/-! # Horizontal gradients agree on constant scalar differences -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace

namespace HeatKernel

/-- Two global energy functions have equal horizontal derivatives almost everywhere where their
scalar representatives differ by a fixed constant. -/
theorem energyGraph_gradient_eq_on_constant_difference {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (u v : energyGraph (N := N) ⊤ X) (c : ℝ) (i : Fin q) :
    ∀ᵐ x ∂volume, (u : GradientSpace (N := N) ⊤ q).fst x =
      (v : GradientSpace (N := N) ⊤ q).fst x + c →
      (u : GradientSpace (N := N) ⊤ q).snd i x = (v : GradientSpace (N := N) ⊤ q).snd i x := by
  have hf : ((u - v : energyGraph (N := N) ⊤ X) : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => (u : GradientSpace (N := N) ⊤ q).fst x - (v : GradientSpace (N := N) ⊤ q).fst x := by
    simpa only [Submodule.coe_sub, WithLp.sub_fst, Pi.sub_def, Opens.coe_top, Measure.restrict_univ]
      using Lp.coeFn_sub (u : GradientSpace (N := N) ⊤ q).fst (v : GradientSpace (N := N) ⊤ q).fst
  have hg : ((u - v : energyGraph (N := N) ⊤ X) : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => (u : GradientSpace (N := N) ⊤ q).snd i x - (v : GradientSpace (N := N) ⊤ q).snd i x := by
    simpa only [Submodule.coe_sub, WithLp.sub_snd, PiLp.sub_apply, Pi.sub_def,
      Opens.coe_top, Measure.restrict_univ] using
      Lp.coeFn_sub ((u : GradientSpace (N := N) ⊤ q).snd i) ((v : GradientSpace (N := N) ⊤ q).snd i)
  filter_upwards [hf, hg, energyGraph_gradient_zero_on_level X hX (u - v) c i] with x hfx hgx hz hx
  have hz0 : ((u - v : energyGraph (N := N) ⊤ X) : GradientSpace (N := N) ⊤ q).fst x = c := by
    rw [hfx, hx]
    ring
  have he := hz hz0
  rw [hgx] at he
  exact sub_eq_zero.mp he



end HeatKernel

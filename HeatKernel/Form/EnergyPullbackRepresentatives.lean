-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LinearGradientPullbacks
import Mathlib.Tactic.Linter

/-! # Identifying coordinate pullbacks by their almost everywhere representatives -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace HeatKernel

/-- Almost everywhere formulas for a function and all its gradients identify a coordinate
pullback with an element of the closed energy graph. -/
theorem gradientPullbackPair_mem_of_representatives {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (T : (Fin N → ℝ) → (Fin N → ℝ))
    (A : SpatialL2 (N := N) ⊤ →L[ℝ] SpatialL2 (N := N) ⊤) (c : ℝ)
    (hA : ∀ f : SpatialL2 (N := N) ⊤, A f =ᵐ[volume] f ∘ T)
    (u z : energyGraph (N := N) ⊤ X)
    (hf : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      (u : GradientSpace (N := N) ⊤ q).fst ∘ T)
    (hg : ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      (fun x => c * (u : GradientSpace (N := N) ⊤ q).snd i (T x))) :
    gradientPullbackPair ⊤ A c (u : GradientSpace (N := N) ⊤ q) ∈ energyGraph ⊤ X := by
  have he : gradientPullbackPair ⊤ A c (u : GradientSpace (N := N) ⊤ q) =
      (z : GradientSpace (N := N) ⊤ q) := by
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · apply Lp.ext
      have H := (hA ((u : GradientSpace (N := N) ⊤ q).fst)).trans hf.symm
      simpa only [gradientPullbackPair, WithLp.toLp_ofLp, WithLp.fst,
        Opens.coe_top, Measure.restrict_univ] using H
    · apply PiLp.ext
      intro i
      apply Lp.ext
      have H : (c • A ((u : GradientSpace (N := N) ⊤ q).snd i) : SpatialL2 (N := N) ⊤)
          =ᵐ[volume] (z : GradientSpace (N := N) ⊤ q).snd i := by
        have hc := Lp.coeFn_smul c (A ((u : GradientSpace (N := N) ⊤ q).snd i))
        simp only [Opens.coe_top, Measure.restrict_univ] at hc
        filter_upwards [hc, hA ((u : GradientSpace (N := N) ⊤ q).snd i), hg i] with x hx hy hz
        simpa only [Pi.smul_apply, smul_eq_mul, Function.comp_def, hy, hz] using hx
      simpa only [gradientPullbackPair, WithLp.toLp_ofLp, WithLp.snd,
        Opens.coe_top, Measure.restrict_univ] using H
  exact he.symm ▸ z.property


end HeatKernel

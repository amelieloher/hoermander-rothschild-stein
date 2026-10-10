-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.GradientPullbacks
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Tactic.Linter

/-! # Bounded linear pullbacks on closed horizontal energy domains -/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace

namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))

/-- The continuous coordinate pullback as a bounded linear map on function-gradient pairs. -/
def gradientPullbackLinearMap (A : SpatialL2 U →L[ℝ] SpatialL2 U) (c : ℝ) :
    GradientSpace U q →L[ℝ] GradientSpace U q where
  toFun := gradientPullbackPair U A c
  map_add' v w := by
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · change A (v + w).fst = A v.fst + A w.fst
      rw [WithLp.add_fst, map_add]
    · apply PiLp.ext
      intro i
      change c • A ((v + w).snd i) = c • A (v.snd i) + c • A (w.snd i)
      rw [WithLp.add_snd, PiLp.add_apply, map_add, smul_add]
  map_smul' r v := by
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · change A (r • v).fst = r • A v.fst
      rw [WithLp.smul_fst, map_smul]
    · apply PiLp.ext
      intro i
      change c • A ((r • v).snd i) = r • (c • A (v.snd i))
      rw [WithLp.smul_snd, PiLp.smul_apply, map_smul, smul_comm c r]
  cont := continuous_gradientPullbackPair U A c

/-- Restriction of a bounded coordinate pullback preserving the closed energy graph. -/
def energyPullbackLinearMap (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (A : SpatialL2 U →L[ℝ] SpatialL2 U) (c : ℝ)
    (hm : ∀ u : energyGraph U X, gradientPullbackPair U A c (u : GradientSpace U q) ∈ energyGraph U X) :
    energyGraph U X →L[ℝ] energyGraph U X :=
  ((gradientPullbackLinearMap U A c).domRestrict (energyGraph U X)).codRestrict
    (energyGraph U X) hm

/-- The bounded energy pullback has the exact bilinear form scaling of its coordinate map. -/
theorem horizontalEnergy_energyPullbackLinearMap
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (A : SpatialL2 U →L[ℝ] SpatialL2 U) (c J : ℝ)
    (hm : ∀ u : energyGraph U X, gradientPullbackPair U A c (u : GradientSpace U q) ∈ energyGraph U X)
    (hA : ∀ f g, inner ℝ (A f) (A g) = J * inner ℝ f g) (u v : energyGraph U X) :
    horizontalEnergy U X (energyPullbackLinearMap U X A c hm u)
      (energyPullbackLinearMap U X A c hm v) = c ^ 2 * J * horizontalEnergy U X u v :=
  horizontalEnergy_pullback_eq U X A c J hA u v _ _ rfl rfl

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LinearGradientPullbacks
public import HeatKernel.Form.BoundedMultiplicationOperators
import Mathlib.Tactic.Linter

/-! # Continuous linear operators with the horizontal Leibniz coordinate formula -/

@[expose] public section

noncomputable section

open MeasureTheory Filter TopologicalSpace
open scoped Topology

namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))

/-- The Leibniz coordinate operator associated with a scalar multiplier and its derivatives. -/
def gradientMultiplierLinearMap (A : SpatialL2 U →L[ℝ] SpatialL2 U)
    (B : Fin q → SpatialL2 U →L[ℝ] SpatialL2 U) : GradientSpace U q →L[ℝ] GradientSpace U q where
  toFun v := WithLp.toLp 2 (A v.fst, WithLp.toLp 2 (fun i => A (v.snd i) + B i v.fst))
  map_add' v w := by
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · change A (v + w).fst = A v.fst + A w.fst
      rw [WithLp.add_fst, map_add]
    · apply PiLp.ext
      intro i
      change A ((v + w).snd i) + B i (v + w).fst =
        (A (v.snd i) + B i v.fst) + (A (w.snd i) + B i w.fst)
      rw [WithLp.add_fst, WithLp.add_snd, PiLp.add_apply, map_add, map_add]
      abel
  map_smul' c v := by
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · change A (c • v).fst = c • A v.fst
      rw [WithLp.smul_fst, map_smul]
    · apply PiLp.ext
      intro i
      change A ((c • v).snd i) + B i (c • v).fst = c • (A (v.snd i) + B i v.fst)
      rw [WithLp.smul_fst, WithLp.smul_snd, PiLp.smul_apply, map_smul, map_smul, smul_add]
  cont := by
    apply continuous_iff_seqContinuous.mpr
    intro v w hv
    have H := (tendsto_GradientSpace_iff U).mp hv
    apply (tendsto_GradientSpace_iff U).mpr
    exact ⟨A.continuous.continuousAt.tendsto.comp H.1, fun i =>
      (A.continuous.continuousAt.tendsto.comp (H.2 i)).add
        ((B i).continuous.continuousAt.tendsto.comp H.1)⟩

/-- Restriction of a Leibniz coordinate operator which preserves the energy graph. -/
def energyMultiplierLinearMap (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (A : SpatialL2 U →L[ℝ] SpatialL2 U) (B : Fin q → SpatialL2 U →L[ℝ] SpatialL2 U)
    (hm : ∀ u : energyGraph U X,
      gradientMultiplierLinearMap U A B (u : GradientSpace U q) ∈ energyGraph U X) :
    energyGraph U X →L[ℝ] energyGraph U X :=
  ((gradientMultiplierLinearMap U A B).domRestrict (energyGraph U X)).codRestrict
    (energyGraph U X) hm

end HeatKernel

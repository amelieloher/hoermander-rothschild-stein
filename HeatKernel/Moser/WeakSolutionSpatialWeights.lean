-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionEnergyTesting
public import HeatKernel.Form.CompactEnergyMultipliers

import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.NormedSpace
import all Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # Spatial weights for nonlinear weak-solution tests

Bounded energy weights with bounded horizontal derivatives act on the same
zero-boundary domain as the time equation. The representative formulas retain
both terms of the horizontal product rule.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped NNReal
namespace HeatKernel

/-- A bounded spatial weight acting on a zero-boundary energy domain. -/
structure WeakSolutionSpatialWeight {N q : ℕ} (V : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) where
  /-- The scalar spatial weight. -/
  toFun : (Fin N → ℝ) → ℝ
  /-- An essential bound on the scalar weight. -/
  bound : ℝ≥0
  /-- Measurability of the scalar weight. -/
  aestronglyMeasurable : AEStronglyMeasurable toFun volume
  /-- The scalar essential bound. -/
  norm_le : ∀ᵐ x ∂volume, ‖toFun x‖ ≤ bound
  /-- Horizontal weak derivatives of the weight. -/
  gradient : Fin q → (Fin N → ℝ) → ℝ
  /-- The continuous energy multiplier. -/
  multiplier : zeroBoundaryGraph V X →L[ℝ] zeroBoundaryGraph V X
  /-- The scalar representative of the multiplier. -/
  value_ae : ∀ z, (multiplier z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
    fun x => toFun x * (z : GradientSpace (N := N) ⊤ q).fst x
  /-- The complete horizontal product rule. -/
  gradient_ae : ∀ z i, (multiplier z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
    fun x => toFun x * (z : GradientSpace (N := N) ⊤ q).snd i x +
      gradient i x * (z : GradientSpace (N := N) ⊤ q).fst x

/-- Compactly supported bounded local energy weights with bounded weak horizontal
derivatives supply spatial weights without a multiplier hypothesis. -/
def WeakSolutionSpatialWeight.ofBoundedWeakGradient {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {ψ : (Fin N → ℝ) → ℝ} {d : Fin q → (Fin N → ℝ) → ℝ}
    (hψ : MemLocalEnergy ⊤ X ψ) (hd : ∀ i, hasWeakWordDeriv X ⊤ [i] ψ (d i))
    (C D : ℝ≥0) (hb : ∀ᵐ x ∂volume, ‖ψ x‖ ≤ C)
    (hdb : ∀ i, ∀ᵐ x ∂volume, ‖d i x‖ ≤ D)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ (V : Set (Fin N → ℝ))) :
    WeakSolutionSpatialWeight V X := by
  have hex := exists_energyMultiplierLinearMap X hX hψ hd
    C.coe_nonneg D.coe_nonneg hb hdb
  let M := Classical.choose hex
  have hM := Classical.choose_spec hex
  have hval (u : energyGraph (N := N) ⊤ X) :
      (M u : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        fun x => ψ x * (u : GradientSpace (N := N) ⊤ q).fst x := (hM u).1
  let K := (compactEnergyMultiplier V X hX hc hs M hval).comp
    (zeroBoundaryEnergyInclusion V X)
  refine ⟨ψ, C, ?_, hb, d, K, ?_, ?_⟩
  · simpa only [Opens.coe_top, Measure.restrict_univ] using hψ.1
  · intro z
    exact hval (zeroBoundaryEnergyInclusion V X z)
  · intro z i
    exact (hM (zeroBoundaryEnergyInclusion V X z)).2 i

/-- The scalar nonlinear test has its literal composition representative. -/
theorem WeakSolutionScalarTest.energyMap_value_ae (T : WeakSolutionScalarTest)
    {N q : ℕ} (V : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (z : zeroBoundaryGraph V X) :
    (T.energyMap V X hX z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => T.toFun ((z : GradientSpace (N := N) ⊤ q).fst x) :=
  piecewiseEnergyComposition_fst_ae X hX T.lipschitz T.map_zero
    T.exceptional T.countable_exceptional T.contDiffAt (zeroBoundaryEnergyInclusion V X z)

/-- The horizontal chain rule includes the chosen derivative at exceptional levels;
the horizontal gradient vanishes on those levels. -/
theorem WeakSolutionScalarTest.energyMap_gradient_ae (T : WeakSolutionScalarTest)
    {N q : ℕ} (V : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (z : zeroBoundaryGraph V X) (i : Fin q) :
    (T.energyMap V X hX z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => deriv T.toFun ((z : GradientSpace (N := N) ⊤ q).fst x) *
        (z : GradientSpace (N := N) ⊤ q).snd i x :=
  piecewiseEnergyComposition_snd_ae X hX T.lipschitz T.map_zero
    T.exceptional T.countable_exceptional T.contDiffAt (zeroBoundaryEnergyInclusion V X z) i

/-- A spatially weighted nonlinear test in the zero-boundary form domain. -/
def WeakSolutionSpatialWeight.energyMap {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} (W : WeakSolutionSpatialWeight V X)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (T : WeakSolutionScalarTest)
    (z : zeroBoundaryGraph V X) : zeroBoundaryGraph V X :=
  W.multiplier (T.energyMap V X hX z)

/-- Spatial weighting preserves continuity of nonlinear energy tests. -/
theorem WeakSolutionSpatialWeight.continuous_energyMap {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (T : WeakSolutionScalarTest) : Continuous (W.energyMap hX T) :=
  W.multiplier.continuous.comp (T.continuous_energyMap V X hX)

/-- The multiplier norm and scalar Lipschitz constant bound the weighted test norm. -/
theorem WeakSolutionSpatialWeight.norm_energyMap_le {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (T : WeakSolutionScalarTest) (z : zeroBoundaryGraph V X) :
    ‖W.energyMap hX T z‖ ≤ (‖W.multiplier‖₊ * T.bound : ℝ≥0) * ‖z‖ := by
  calc
    ‖W.energyMap hX T z‖ ≤ ‖W.multiplier‖ * ‖T.energyMap V X hX z‖ :=
      W.multiplier.le_opNorm (T.energyMap V X hX z)
    _ ≤ ‖W.multiplier‖ * ((T.bound : ℝ) * ‖z‖) :=
      mul_le_mul_of_nonneg_left (T.norm_energyMap_le V X hX z) ‖W.multiplier‖₊.coe_nonneg
    _ = (‖W.multiplier‖₊ * T.bound : ℝ≥0) * ‖z‖ := by
      simp only [NNReal.coe_mul, coe_nnnorm]
      ring

/-- The weighted nonlinear test has its pointwise scalar product representative. -/
theorem WeakSolutionSpatialWeight.energyMap_value_ae {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (T : WeakSolutionScalarTest) (z : zeroBoundaryGraph V X) :
    (W.energyMap hX T z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => W.toFun x * T.toFun ((z : GradientSpace (N := N) ⊤ q).fst x) := by
  filter_upwards [W.value_ae (T.energyMap V X hX z), T.energyMap_value_ae V X hX z]
    with x hx hy
  exact hx.trans (congrArg (W.toFun x * ·) hy)

/-- The weighted test retains the principal chain-rule term and the weight-gradient term. -/
theorem WeakSolutionSpatialWeight.energyMap_gradient_ae {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (T : WeakSolutionScalarTest) (z : zeroBoundaryGraph V X) (i : Fin q) :
    (W.energyMap hX T z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => W.toFun x * (deriv T.toFun ((z : GradientSpace (N := N) ⊤ q).fst x) *
        (z : GradientSpace (N := N) ⊤ q).snd i x) +
        W.gradient i x * T.toFun ((z : GradientSpace (N := N) ⊤ q).fst x) := by
  filter_upwards [W.gradient_ae (T.energyMap V X hX z) i,
    T.energyMap_value_ae V X hX z, T.energyMap_gradient_ae V X hX z i] with x hx hy hz
  exact hx.trans (by rw [hy, hz])

end HeatKernel

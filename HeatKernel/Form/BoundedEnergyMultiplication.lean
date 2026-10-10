-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.GradientMultiplicationOperators
public import HeatKernel.Form.BoundedWeakMultipliers
import Mathlib.Tactic.Linter

/-! # Bounded local multipliers acting continuously on the horizontal energy domain -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace RothschildStein

namespace HeatKernel

variable {N q : ℕ}

/-- Scalar representatives determine the full Leibniz coordinate formula. -/
theorem gradientMultiplierLinearMap_ae
    (A : SpatialL2 (N := N) ⊤ →L[ℝ] SpatialL2 (N := N) ⊤)
    (B : Fin q → SpatialL2 (N := N) ⊤ →L[ℝ] SpatialL2 (N := N) ⊤)
    (φ : (Fin N → ℝ) → ℝ) (g : Fin q → (Fin N → ℝ) → ℝ)
    (hA : ∀ f : SpatialL2 (N := N) ⊤, A f =ᵐ[volume] (fun x => φ x * f x))
    (hB : ∀ i (f : SpatialL2 (N := N) ⊤), B i f =ᵐ[volume] (fun x => g i x * f x))
    (u : GradientSpace (N := N) ⊤ q) :
    (gradientMultiplierLinearMap ⊤ A B u).fst =ᵐ[volume] (fun x => φ x * u.fst x) ∧
      ∀ i, (gradientMultiplierLinearMap ⊤ A B u).snd i =ᵐ[volume]
        (fun x => φ x * u.snd i x + g i x * u.fst x) := by
  refine ⟨hA u.fst, fun i => ?_⟩
  have h := Lp.coeFn_add (A (u.snd i)) (B i u.fst)
  simp only [Opens.coe_top, Measure.restrict_univ] at h
  exact h.trans ((hA (u.snd i)).add (hB i u.fst))

/-- The Leibniz coordinate operator preserves the closed energy graph under the bounded
local multiplier hypotheses. -/
theorem gradientMultiplierLinearMap_mem_energyGraph
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {φ : (Fin N → ℝ) → ℝ} {g : Fin q → (Fin N → ℝ) → ℝ}
    (hφ : MemLocalEnergy ⊤ X φ) (hw : ∀ i, hasWeakWordDeriv X ⊤ [i] φ (g i))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ᵐ x ∂volume, ‖φ x‖ ≤ C) (hgb : ∀ i, ∀ᵐ x ∂volume, ‖g i x‖ ≤ D)
    (A : SpatialL2 (N := N) ⊤ →L[ℝ] SpatialL2 (N := N) ⊤)
    (B : Fin q → SpatialL2 (N := N) ⊤ →L[ℝ] SpatialL2 (N := N) ⊤)
    (hA : ∀ f : SpatialL2 (N := N) ⊤, A f =ᵐ[volume] (fun x => φ x * f x))
    (hB : ∀ i (f : SpatialL2 (N := N) ⊤), B i f =ᵐ[volume] (fun x => g i x * f x))
    (u : energyGraph (N := N) ⊤ X) :
    gradientMultiplierLinearMap ⊤ A B (u : GradientSpace (N := N) ⊤ q) ∈ energyGraph ⊤ X := by
  obtain ⟨z, hzf, hzg⟩ := exists_energyGraph_mul_bounded_local X hX u hφ hw hC hD hb hgb
  have H := gradientMultiplierLinearMap_ae A B φ g hA hB (u : GradientSpace (N := N) ⊤ q)
  have he : gradientMultiplierLinearMap ⊤ A B (u : GradientSpace (N := N) ⊤ q) =
      (z : GradientSpace (N := N) ⊤ q) := by
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · apply Lp.ext
      simpa only [WithLp.fst, Opens.coe_top, Measure.restrict_univ] using H.1.trans hzf.symm
    · apply PiLp.ext
      intro i
      apply Lp.ext
      simpa only [WithLp.snd, Opens.coe_top, Measure.restrict_univ] using (H.2 i).trans (hzg i).symm
  exact he.symm ▸ z.property

/-- Local bounded functions with bounded horizontal derivatives act by bounded real linear
operators on the global energy domain. -/
theorem exists_energyMultiplierLinearMap
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {φ : (Fin N → ℝ) → ℝ} {g : Fin q → (Fin N → ℝ) → ℝ}
    (hφ : MemLocalEnergy ⊤ X φ) (hw : ∀ i, hasWeakWordDeriv X ⊤ [i] φ (g i))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ᵐ x ∂volume, ‖φ x‖ ≤ C) (hgb : ∀ i, ∀ᵐ x ∂volume, ‖g i x‖ ≤ D) :
    ∃ M : energyGraph (N := N) ⊤ X →L[ℝ] energyGraph (N := N) ⊤ X,
      ∀ u, energyInclusion ⊤ X (M u) =ᵐ[volume] (fun x => φ x * energyInclusion ⊤ X u x) ∧
        ∀ i, (energyGradient ⊤ X (M u)) i =ᵐ[volume]
          (fun x => φ x * (energyGradient ⊤ X u) i x + g i x * energyInclusion ⊤ X u x) := by
  let μ := volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))
  have hb' : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C := by
    simpa only [μ, Opens.coe_top, Measure.restrict_univ] using hb
  have hgb' : ∀ i, ∀ᵐ x ∂μ, ‖g i x‖ ≤ D := by
    simpa only [μ, Opens.coe_top, Measure.restrict_univ] using hgb
  have hg : ∀ i, AEStronglyMeasurable (g i) μ :=
    fun i => (hw i).2.1.aestronglyMeasurable
  let A := boundedL2MulContinuousLinearMap hφ.1 hC hb'
  let B := fun i => boundedL2MulContinuousLinearMap (hg i) hD (hgb' i)
  have hA : ∀ f : SpatialL2 (N := N) ⊤, A f =ᵐ[volume] (fun x => φ x * f x) := by
    intro f
    simpa only [A, boundedL2MulContinuousLinearMap_apply, μ, Opens.coe_top, Measure.restrict_univ]
      using boundedL2Mul_ae hφ.1 hC hb' f
  have hB : ∀ i (f : SpatialL2 (N := N) ⊤), B i f =ᵐ[volume] (fun x => g i x * f x) := by
    intro i f
    simpa only [B, boundedL2MulContinuousLinearMap_apply, μ, Opens.coe_top, Measure.restrict_univ]
      using boundedL2Mul_ae (hg i) hD (hgb' i) f
  let M := energyMultiplierLinearMap ⊤ X A B
    (gradientMultiplierLinearMap_mem_energyGraph X hX hφ hw hC hD hb hgb A B hA hB)
  exact ⟨M, fun u => gradientMultiplierLinearMap_ae A B φ g hA hB
    (u : GradientSpace (N := N) ⊤ q)⟩



end HeatKernel

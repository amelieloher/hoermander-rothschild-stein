-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ScalarComposition
public import HeatKernel.Form.GraphForm
import Mathlib.Tactic.Linter
import Mathlib.Tactic.Ring

/-! # Continuous pullbacks of the closed horizontal gradient graph -/

@[expose] public section

noncomputable section

open MeasureTheory Filter TopologicalSpace
open scoped Topology

namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))

/-- Apply a continuous scalar pullback to every coordinate, with an additional derivative scale. -/
def gradientPullbackPair (A : SpatialL2 U →L[ℝ] SpatialL2 U) (c : ℝ)
    (v : GradientSpace U q) : GradientSpace U q :=
  WithLp.toLp 2 (A v.fst, WithLp.toLp 2 (fun i => c • A (v.snd i)))

/-- Continuous scalar pullbacks preserve convergence of function-gradient pairs. -/
theorem tendsto_gradientPullbackPair (A : SpatialL2 U →L[ℝ] SpatialL2 U) (c : ℝ)
    {v : ℕ → GradientSpace U q} {w : GradientSpace U q} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => gradientPullbackPair U A c (v n)) atTop (𝓝 (gradientPullbackPair U A c w)) := by
  have H := (tendsto_GradientSpace_iff U).mp hv
  apply (tendsto_GradientSpace_iff U).mpr
  exact ⟨A.continuous.continuousAt.tendsto.comp H.1,
    fun i => (A.continuous.continuousAt.tendsto.comp (H.2 i)).const_smul c⟩

/-- The coordinate pullback is continuous in the graph norm. -/
theorem continuous_gradientPullbackPair (A : SpatialL2 U →L[ℝ] SpatialL2 U) (c : ℝ) :
    Continuous (gradientPullbackPair (q := q) U A c) := by
  apply continuous_iff_seqContinuous.mpr
  intro v w hv
  exact tendsto_gradientPullbackPair U A c hv

/-- A continuous pullback preserving the smooth core preserves its closed gradient graph. -/
theorem gradientPullbackPair_mem_energyGraph
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (A : SpatialL2 U →L[ℝ] SpatialL2 U) (c : ℝ)
    (hcore : ∀ v ∈ smoothGradientPairs U X, gradientPullbackPair U A c v ∈ energyGraph U X)
    (u : energyGraph U X) : gradientPullbackPair U A c (u : GradientSpace U q) ∈ energyGraph U X := by
  obtain ⟨v, hv, ht⟩ := exists_smoothGradientPairs_tendsto U X u
  exact (isClosed_energyGraph U X).mem_of_tendsto (tendsto_gradientPullbackPair U A c ht)
    (Eventually.of_forall fun n => hcore (v n) (hv n))

/-- The horizontal energy scales by the scalar pullback's inner-product factor and by the
square of the derivative scale. -/
theorem horizontalEnergy_pullback_eq
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (A : SpatialL2 U →L[ℝ] SpatialL2 U) (c J : ℝ)
    (hA : ∀ f g, inner ℝ (A f) (A g) = J * inner ℝ f g)
    (u v z w : energyGraph U X)
    (hz : (z : GradientSpace U q) = gradientPullbackPair U A c (u : GradientSpace U q))
    (hw : (w : GradientSpace U q) = gradientPullbackPair U A c (v : GradientSpace U q)) :
    horizontalEnergy U X z w = c ^ 2 * J * horizontalEnergy U X u v := by
  simp only [horizontalEnergy, energyGradient_apply, hz, hw, gradientPullbackPair,
    WithLp.toLp_snd, PiLp.inner_apply,
    real_inner_smul_left, real_inner_smul_right, hA]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring


end HeatKernel

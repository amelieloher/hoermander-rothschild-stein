-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.MetricBallBoundary
public import HeatKernel.Poincare.PathCoverChain
public import Mathlib.Topology.Order.IntermediateValue

/-! Simple Whitney intersection chains supported on radial minimizing segments. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace HeatKernel

/-- The selected balls whose fivefold dilates meet a path image. -/
def boundaryBallsMeetingPath {E T : Type*} [PseudoMetricSpace E]
    (C U : Set E) (κ : ℝ) (γ : T → E) : Set E :=
  {w ∈ C | (ball w (5 * (infDist w Uᶜ / κ)) ∩ range γ).Nonempty}

/-- A radial metric segment joins its starting Whitney ball to any selected ball whose
fivefold dilate contains the center, through a finite simple chain of meeting balls. -/
theorem exists_simple_boundaryBall_chain {E : Type*} [MetricSpace E]
    {x z z₀ : E} {r κ : ℝ} {C : Set E} (hκ : 0 < κ)
    (hcompl : (ball x r)ᶜ.Nonempty) (hCU : C ⊆ ball x r)
    (hcover : ball x r = ⋃ w ∈ C, ball w (5 * (infDist w (ball x r)ᶜ / κ)))
    (hzC : z ∈ C) (hrootC : z₀ ∈ C)
    (hroot : x ∈ ball z₀ (5 * (infDist z₀ (ball x r)ᶜ / κ)))
    {γ : Icc (0 : ℝ) 1 → E}
    (hzero : γ ⟨0, by norm_num⟩ = z) (hone : γ ⟨1, by norm_num⟩ = x)
    (hγ : ∀ s t, dist (γ s) (γ t) = dist z x * dist s t) :
    let I := boundaryBallsMeetingPath C (ball x r) κ γ
    ∃ (hzI : z ∈ I) (hrootI : z₀ ∈ I),
      ∃ p : (intersectionGraph (fun w : I => ball w.val
        (5 * (infDist w.val (ball x r)ᶜ / κ)))).Walk ⟨z, hzI⟩ ⟨z₀, hrootI⟩, p.IsPath := by
  classical
  let I := boundaryBallsMeetingPath C (ball x r) κ γ
  let o : Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let e : Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  have hzrad : 0 < infDist z (ball x r)ᶜ / κ := div_pos
    ((isOpen_ball.isClosed_compl.notMem_iff_infDist_pos hcompl).mp
      (by simpa using hCU hzC)) hκ
  have hzball : z ∈ ball z (5 * (infDist z (ball x r)ᶜ / κ)) :=
    mem_ball_self (mul_pos (by norm_num) hzrad)
  have hzI : z ∈ I := ⟨hzC, z, hzball, o, hzero⟩
  have hrootI : z₀ ∈ I := ⟨hrootC, x, hroot, e, hone⟩
  refine ⟨hzI, hrootI, ?_⟩
  let V := fun w : I => ball w.val (5 * (infDist w.val (ball x r)ᶜ / κ))
  have hc : Continuous γ := (LipschitzWith.of_dist_le_mul
    (K := ⟨dist z x, dist_nonneg⟩) (fun s t => (hγ s t).le)).continuous
  have : PreconnectedSpace (Icc (0 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hpathcover : ∀ t, ∃ w : I, γ t ∈ V w := by
    intro t
    have ht := (metric_segment_boundary_bounds (hCU hzC) hcompl hzero hone hγ t).1
    rw [hcover] at ht
    obtain ⟨w, hwC, hwt⟩ := mem_iUnion₂.mp ht
    exact ⟨⟨w, hwC, γ t, hwt, t, rfl⟩, hwt⟩
  apply exists_simple_chain_of_preconnected_image_cover V (fun _ => isOpen_ball) γ hc hpathcover
    ⟨z, hzI⟩ ⟨z₀, hrootI⟩
  · refine ⟨o, ?_⟩
    change γ o ∈ ball z (5 * (infDist z (ball x r)ᶜ / κ))
    rw [show γ o = z from hzero]
    exact hzball
  · refine ⟨e, ?_⟩
    change γ e ∈ ball z₀ (5 * (infDist z₀ (ball x r)ᶜ / κ))
    rw [show γ e = x from hone]
    exact hroot

end HeatKernel

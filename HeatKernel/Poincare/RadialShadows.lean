-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WhitneyShadows

/-! Nonnegative measure bounds for full radial Whitney shadows. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal BigOperators

namespace HeatKernel

/-- Full radial meeting shadows satisfy the homogeneous shadow bound. The volume formula
and complement nonemptiness are explicit geometric inputs. -/
theorem tsum_measure_boundaryBall_radial_shadow_le_of_volume {E : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (Q : ℕ) (v : ℝ≥0∞)
    (hvolume : ∀ z : E, ∀ s : ℝ, 0 < s → μ (ball z s) = ENNReal.ofReal (s ^ Q) * v)
    {x w : E} {r κ : ℝ} {C : Set E} (hκ : 10 < κ)
    (hcompl : (ball x r)ᶜ.Nonempty) (hCU : C ⊆ ball x r) (hwC : w ∈ C)
    (hdisj : C.PairwiseDisjoint fun z => ball z (infDist z (ball x r)ᶜ / κ))
    (γ : C → Icc (0 : ℝ) 1 → E)
    (hzero : ∀ z : C, γ z ⟨0, by norm_num⟩ = z.val)
    (hone : ∀ z : C, γ z ⟨1, by norm_num⟩ = x)
    (hγ : ∀ z : C, ∀ t u, dist (γ z t) (γ z u) = dist z.val x * dist t u) :
    (∑' z : {z : C | (ball w (5 * (infDist w (ball x r)ᶜ / κ)) ∩ range (γ z)).Nonempty},
      μ (ball z.val.val (infDist z.val.val (ball x r)ᶜ / κ))) ≤
      ENNReal.ofReal ((κ + 13) ^ Q) * μ (ball w (infDist w (ball x r)ᶜ / κ)) := by
  have ha : 0 < infDist w (ball x r)ᶜ / κ := div_pos
    ((isOpen_ball.isClosed_compl.notMem_iff_infDist_pos hcompl).mp
      (by simpa using hCU hwC)) (by linarith)
  let S := {z : C | (ball w (5 * (infDist w (ball x r)ᶜ / κ)) ∩ range (γ z)).Nonempty}
  apply tsum_measure_le_homogeneous_radial_shadow (ι := S) μ Q v hvolume
    (fun z : S => z.val.val) (fun z : S => infDist z.val.val (ball x r)ᶜ / κ) w ha
    (by linarith)
  · intro z t hzt
    apply hdisj z.val.property t.val.property
    intro heq
    exact hzt (Subtype.ext (Subtype.ext heq))
  · intro z
    have hb := (boundaryBall_bounds_of_radial_segment_meeting hκ (hCU z.val.property)
      hcompl (hzero z.val) (hone z.val) (hγ z.val) z.property).1
    linarith
  · intro z
    exact (boundaryBall_bounds_of_radial_segment_meeting hκ (hCU z.val.property)
      hcompl (hzero z.val) (hone z.val) (hγ z.val) z.property).2.1

end HeatKernel

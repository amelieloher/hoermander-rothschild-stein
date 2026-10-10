-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linter

/-! # Closed convex sublevels of positive quadratic forms -/

@[expose] public section

noncomputable section

open Set

namespace HeatKernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ)

/-- A positive symmetric continuous bilinear form has convex quadratic sublevels. -/
theorem convex_bilinear_self_sublevel (hsym : ∀ u v, B u v = B v u)
    (hpos : ∀ u, 0 ≤ B u u) (c : ℝ) : Convex ℝ {u | B u u ≤ c} := by
  intro u hu v hv s t hs ht hst
  change B (s • u + t • v) (s • u + t • v) ≤ c
  have hid : B (s • u + t • v) (s • u + t • v) =
      s * B u u + t * B v v - s * t * B (u - v) (u - v) := by
    have hse : s = 1 - t := by linarith
    rw [hse]
    simp only [map_add, map_sub, map_smul, add_apply,
      sub_apply, smul_apply, smul_eq_mul, hsym v u]
    ring
  rw [hid]
  have hp := mul_nonneg (mul_nonneg hs ht) (hpos (u - v))
  have hu' := mul_le_mul_of_nonneg_left hu hs
  have hv' := mul_le_mul_of_nonneg_left hv ht
  calc
    _ ≤ s * c + t * c := by linarith
    _ = c := by rw [← add_mul, hst, one_mul]

/-- Continuity of a bilinear form makes every quadratic sublevel norm closed. -/
theorem isClosed_bilinear_self_sublevel (c : ℝ) : IsClosed {u | B u u ≤ c} :=
  isClosed_le (B.continuous.clm_apply continuous_id) continuous_const


end HeatKernel

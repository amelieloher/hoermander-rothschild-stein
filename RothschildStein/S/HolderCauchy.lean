-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderBounds
public import Mathlib.Topology.MetricSpace.Cauchy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped ENNReal Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- The Cauchy condition for the exact full Hölder
norm, stated directly on function representatives (BB Prop 2.15, p. 82).
Exterior values are ignored; limits are pointwise on the domain. -/
def holderCauchySeq
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (α : ℝ)
    (V : Set (Fin n → ℝ)) (F : ℕ → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m ≥ N,∀ j ≥ N,
    holderENorm d α V (fun x => F m x-F j x) ≤ ENNReal.ofReal ε

/-- Hölder Cauchy sequences are pointwise Cauchy on their
actual domain (BB Prop 2.15, p. 82; direct Cauchy proof). -/
theorem holderCauchySeq_pointwise
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (α : ℝ)
    (V : Set (Fin n → ℝ)) (F : ℕ → (Fin n → ℝ) → ℝ)
    (h : holderCauchySeq d α V F) {x : Fin n → ℝ} (hx : x ∈ V) :
    CauchySeq (fun j => F j x) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε he
  obtain ⟨N,hN⟩ := h (ε/2) (half_pos he)
  refine ⟨N,fun m hm j hj => ?_⟩
  have H := (enorm_le_holderENorm d α V (fun y => F m y-F j y) hx).trans (hN m hm j hj)
  have hr : |F m x-F j x| ≤ ε/2 := by
    exact (ENNReal.ofReal_le_ofReal_iff (half_pos he).le).mp H
  simpa only [Real.dist_eq] using hr.trans_lt (half_lt_self he)

end RothschildStein.S

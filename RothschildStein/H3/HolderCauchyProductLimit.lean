-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderCauchy
public import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology ENNReal
namespace RothschildStein.H3

/-- A two-index limit of full Hölder differences gives the
scalar Cauchy condition used by the shared completeness theorem. -/
theorem holderCauchySeq_of_product_limit {N : ℕ}
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞) (α : ℝ)
    (U : Set (Fin N → ℝ)) (F : ℕ → (Fin N → ℝ) → ℝ)
    (h : Tendsto (fun p : ℕ × ℕ =>
      holderENorm d α U (fun x => F p.1 x - F p.2 x))
      (atTop ×ˢ atTop) (𝓝 0)) : S.holderCauchySeq d α U F := by
  intro ε hε
  have he : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hev := h.eventually (gt_mem_nhds he)
  obtain ⟨P, hP, Q, hQ, hpq⟩ := eventually_prod_iff.mp hev
  obtain ⟨n, hn⟩ := eventually_atTop.mp hP
  obtain ⟨m, hm⟩ := eventually_atTop.mp hQ
  refine ⟨max n m, fun i hi j hj => ?_⟩
  exact (hpq (hn i ((le_max_left n m).trans hi))
    (hm j ((le_max_right n m).trans hj))).le

end RothschildStein.H3

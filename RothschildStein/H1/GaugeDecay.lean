-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.HomogeneousBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Euclidean escape forces escape from every
homogeneous-norm sublevel (BB Proposition 3.9, p. 100). -/
theorem gauge_large_of_norm_large (ν : G2.HomogeneousNorm G) (A : ℝ) :
    ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → A < ν x := by
  obtain ⟨B, hB⟩ := (G2.isCompact_gauge_le ν.gauge A).exists_bound_of_continuousOn continuous_id.continuousOn
  refine ⟨B + 1, fun x hx => ?_⟩
  by_contra hn
  have hb := hB x (le_of_not_gt hn)
  simp only [id_eq] at hb
  linarith

/-- A negative-degree gauge bound outside a gauge ball implies Euclidean
decay at infinity (BB pp. 270–271). -/
theorem decay_of_gauge_power_bound (ν : G2.HomogeneousNorm G) {a C A : ℝ}
    (ha : a < 0) {f : (Fin N → ℝ) → ℝ}
    (hb : ∀ x, A ≤ ν x → |f x| ≤ C * (ν x) ^ a) :
    ∀ ε > 0, ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → ‖f x‖ ≤ ε := by
  have ht : Tendsto (fun t : ℝ => C * t ^ a) atTop (𝓝 0) := by
    have hp := tendsto_rpow_neg_atTop (neg_pos.mpr ha)
    simpa only [neg_neg, mul_zero] using hp.const_mul C
  intro ε hε
  have he : ∀ᶠ t : ℝ in atTop, C * t ^ a < ε := ht.eventually (gt_mem_nhds hε)
  obtain ⟨B, hB⟩ := eventually_atTop.mp he
  obtain ⟨R, hR⟩ := gauge_large_of_norm_large G ν (max A B)
  refine ⟨R, fun x hx => ?_⟩
  have hν := hR x hx
  have hA : A ≤ ν x := (le_max_left _ _).trans hν.le
  have hB' : B ≤ ν x := (le_max_right _ _).trans hν.le
  rw [Real.norm_eq_abs]
  exact (hb x hA).trans (hB _ hB').le

end RothschildStein.H1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.HomogeneousPacking

/-! Finiteness of bounded disjoint ball families with a positive lower radius. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

namespace HeatKernel

/-- Exact homogeneous volume makes every bounded disjoint family with a positive
uniform lower radius finite, without requiring an integer containing-radius ratio. -/
theorem finite_of_bounded_homogeneous_ball_packing {E ι : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (Q : ℕ) (v : ℝ≥0∞)
    (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (hvolume : ∀ x : E, ∀ r : ℝ, 0 < r → μ (ball x r) = ENNReal.ofReal (r ^ Q) * v)
    {I : Set ι} (z : ι → E) (a : ι → ℝ) (x : E) {h R : ℝ} (hh : 0 < h)
    (hdisj : I.PairwiseDisjoint fun i => ball (z i) (a i))
    (hlower : ∀ i ∈ I, h ≤ a i) (hsub : ∀ i ∈ I, ball (z i) (a i) ⊆ ball x R) : I.Finite := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max (R / h) 0)
  have hkpos : 0 < k := by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hk)
  have hR : R ≤ (k : ℝ) * h :=
    ((div_lt_iff₀ hh).mp ((le_max_left _ _).trans_lt hk)).le
  exact finite_of_homogeneous_ball_packing μ Q v hv0 hvtop hvolume z a x hh k hkpos hdisj
    hlower (fun i hi => (hsub i hi).trans (ball_subset_ball hR))

end HeatKernel

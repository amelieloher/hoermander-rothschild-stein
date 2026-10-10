-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.MetricGeodesic

/-! Exact distance identities for optimal paths on the unit interval. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace HeatKernel

/-- An optimal Lipschitz path between its endpoints has the exact constant-speed distance
identity on every subinterval, by the triangle inequality. -/
theorem metric_path_dist_eq_of_optimal_bound {E : Type*} [PseudoMetricSpace E]
    {x y : E} {γ : Icc (0 : ℝ) 1 → E}
    (hx : γ ⟨0, by norm_num⟩ = x) (hy : γ ⟨1, by norm_num⟩ = y)
    (hγ : ∀ s t, dist (γ s) (γ t) ≤ dist x y * dist s t) :
    ∀ s t, dist (γ s) (γ t) = dist x y * dist s t := by
  let z : Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let o : Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  have hordered : ∀ s t : Icc (0 : ℝ) 1, (s : ℝ) ≤ t →
      dist (γ s) (γ t) = dist x y * dist s t := by
    intro s t hst
    have hzs : dist z s = (s : ℝ) := by
      change |0 - (s : ℝ)| = (s : ℝ)
      rw [zero_sub, abs_neg, abs_of_nonneg s.2.1]
    have hto : dist t o = 1 - (t : ℝ) := by
      change |(t : ℝ) - 1| = 1 - (t : ℝ)
      rw [abs_of_nonpos (sub_nonpos.mpr t.2.2)]
      ring
    have hst' : dist s t = (t : ℝ) - s := by
      change |(s : ℝ) - t| = (t : ℝ) - s
      rw [abs_of_nonpos (sub_nonpos.mpr hst)]
      ring
    have hleft := hγ z s
    have hright := hγ t o
    have hmiddle := hγ s t
    have htri : dist (γ z) (γ o) ≤
        dist (γ z) (γ s) + dist (γ s) (γ t) + dist (γ t) (γ o) := by
      have h₁ := dist_triangle (γ z) (γ s) (γ o)
      have h₂ := dist_triangle (γ s) (γ t) (γ o)
      linarith
    rw [show γ z = x from hx, show γ o = y from hy] at htri
    rw [show γ z = x from hx] at hleft
    rw [show γ o = y from hy] at hright
    rw [hzs] at hleft
    rw [hto] at hright
    rw [hst'] at hmiddle ⊢
    nlinarith
  intro s t
  rcases le_total (s : ℝ) t with hst | hts
  · exact hordered s t hst
  · simpa only [dist_comm] using hordered t s hts

/-- Properness and arbitrarily close constant-speed competitors give a minimizing
constant-speed metric segment. -/
theorem exists_metric_segment_of_approximate_paths {E : Type*} [MetricSpace E]
    [ProperSpace E] (x y : E)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ γ : Icc (0 : ℝ) 1 → E,
        γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (γ s) (γ t) ≤ (dist x y + ε) * dist s t) :
    ∃ γ : Icc (0 : ℝ) 1 → E,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (γ s) (γ t) = dist x y * dist s t := by
  obtain ⟨γ, hx, hy, hγ⟩ := exists_optimal_metric_path_of_approximate_paths x y happrox
  exact ⟨γ, hx, hy, metric_path_dist_eq_of_optimal_bound hx hy hγ⟩

end HeatKernel

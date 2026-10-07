-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Asymptotics.Ring

@[expose] public section
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace RothschildStein.G3

theorem taylor_leading_term_of_lower_jets_zero (f : ℝ → ℝ) (k : ℕ)
    (h : ∀ j < k, iteratedDeriv j f 0 = 0) (t : ℝ) :
    taylorWithinEval f k Set.univ 0 t =
      ((k.factorial : ℝ)⁻¹ * iteratedDeriv k f 0) * t ^ k := by
  rw [taylor_within_apply]
  simp only [iteratedDerivWithin_univ, sub_zero, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · ring
  · intro j hj hjk
    have hjlt : j < k := by simp only [Finset.mem_range] at hj; omega
    rw [h j hjlt, mul_zero]
  · simp

theorem scalar_coefficient_zero_of_littleO (a : ℝ) (k : ℕ)
    (h : (fun t : ℝ => a * t ^ k) =o[𝓝 0] (fun t => t ^ k)) : a = 0 := by
  by_contra ha
  have hh := (isLittleO_const_mul_left_iff ha).mp h
  have hn : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ^ k ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact pow_ne_zero k ht
  exact isLittleO_irrefl hn.frequently (hh.mono nhdsWithin_le_nhds)

end RothschildStein.G3

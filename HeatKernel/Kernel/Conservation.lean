-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # Conservation from scaling and semigroup mass identities

Dilation makes the mass constant on positive times. Multiplicativity makes that constant
idempotent, and a nonzero strong-continuity pairing excludes the zero alternative.
-/

@[expose] public section

open Filter
open scoped Topology

namespace HeatKernel

/-- Parabolic dilation makes a time-dependent scalar constant on positive times. -/
theorem eq_of_parabolic_scaling (m : ℝ → ℝ)
    (hscale : ∀ r t, 0 < r → 0 < t → m (r ^ 2 * t) = m t)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) : m s = m t := by
  have hr : 0 < Real.sqrt (s / t) := Real.sqrt_pos.mpr (div_pos hs ht)
  have heq : Real.sqrt (s / t) ^ 2 * t = s := by
    rw [Real.sq_sqrt (div_nonneg hs.le ht.le), div_mul_cancel₀ _ ht.ne']
  simpa only [heq] using hscale (Real.sqrt (s / t)) t hr ht

/-- A nonzero parabolically invariant multiplicative mass is one at every positive time. -/
theorem mass_eq_one_of_scaling_and_add (m : ℝ → ℝ)
    (hscale : ∀ r t, 0 < r → 0 < t → m (r ^ 2 * t) = m t)
    (hadd : ∀ s t, 0 < s → 0 < t → m (s + t) = m s * m t)
    (hne : ∃ t, 0 < t ∧ m t ≠ 0) {s : ℝ} (hs : 0 < s) : m s = 1 := by
  obtain ⟨t, ht, hmt⟩ := hne
  have hid : m t * m t = m t :=
    (hadd t t ht ht).symm.trans (eq_of_parabolic_scaling m hscale (add_pos ht ht) ht)
  have hone : m t = 1 := mul_left_cancel₀ hmt (hid.trans (mul_one (m t)).symm)
  exact (eq_of_parabolic_scaling m hscale hs ht).trans hone

/-- A pairing with a nonzero limit excludes identically zero mass at positive times. -/
theorem exists_nonzero_mass_of_tendsto_pairing (m a : ℝ → ℝ) {c : ℝ}
    (hc : c ≠ 0) (ha : Tendsto a (𝓝[>] 0) (𝓝 c))
    (hzero : ∀ t, 0 < t → m t = 0 → a t = 0) : ∃ t, 0 < t ∧ m t ≠ 0 := by
  by_contra h
  have hm : ∀ t, 0 < t → m t = 0 := by
    simpa only [not_exists, not_and, not_not] using h
  have heq : a =ᶠ[𝓝[>] 0] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hzero t ht (hm t ht)
  have hz : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 c) := ha.congr' heq
  exact hc (tendsto_nhds_unique hz tendsto_const_nhds)

/-- Scaling, the mass composition identity, and strong-continuity pairing imply conservation. -/
theorem mass_eq_one_of_scaling_add_and_pairing (m a : ℝ → ℝ) {c : ℝ}
    (hscale : ∀ r t, 0 < r → 0 < t → m (r ^ 2 * t) = m t)
    (hadd : ∀ s t, 0 < s → 0 < t → m (s + t) = m s * m t)
    (hc : c ≠ 0) (ha : Tendsto a (𝓝[>] 0) (𝓝 c))
    (hzero : ∀ t, 0 < t → m t = 0 → a t = 0) {s : ℝ} (hs : 0 < s) : m s = 1 :=
  mass_eq_one_of_scaling_and_add m hscale hadd
    (exists_nonzero_mass_of_tendsto_pairing m a hc ha hzero) hs

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierPointwise
public import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- A function continuous at the origin with a strictly negative dyadic degree vanishes. This is the rigidity step after the smooth null solution is smooth by the local weak regularity theorem (BB p. 266). -/
theorem eq_zero_of_dyadic_scaling {f : (Fin N → ℝ) → ℝ}
    (hf : ContinuousAt f 0) {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hscale : ∀ x, f (G.dilate 2 x) = c * f x) : f = 0 := by
  funext x
  have he (n : ℕ) : f x = c ^ n * f (G.dilate ((1 / 2 : ℝ) ^ n) x) := by
    induction n with
    | zero => simp only [pow_zero, G2.dilate_one, one_mul]
    | succ n ih =>
      have h := hscale (G.dilate ((1 / 2 : ℝ) ^ (n + 1)) x)
      have hd : 2 * (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) ^ n := by
        rw [pow_succ]; ring
      rw [G2.dilate_dilate, hd] at h
      rw [ih, h, pow_succ]
      ring
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hd := ((G2.continuous_dilate_parameter G x).tendsto 0).comp ht
  simp only [G2.zero_dilate] at hd
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc1).mul (hf.tendsto.comp hd)
  simp only [zero_mul] at hp
  have hconst : Tendsto (fun _ : ℕ => f x) atTop (𝓝 0) := by
    exact hp.congr' (Eventually.of_forall fun n => (he n).symm)
  exact tendsto_nhds_unique tendsto_const_nhds hconst

end RothschildStein.H1

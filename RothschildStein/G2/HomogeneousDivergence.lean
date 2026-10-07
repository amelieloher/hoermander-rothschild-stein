-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.InvariantDivergence
public import Mathlib.Topology.Algebra.Order.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open Filter
open scoped Topology
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Dilating a fixed point by a parameter tending to zero tends to the identity. -/
theorem continuousAt_dilate_parameter_zero (x : Fin N → ℝ) :
    ContinuousAt (fun t : ℝ => G.dilate t x) 0 := by
  apply continuousAt_pi.mpr
  intro j
  exact (continuousAt_id.pow (G.weight j)).mul continuousAt_const

/-- A continuous function of negative homogeneous degree vanishes
(BB Remark 3.30, p. 111; valid for every positive real degree). -/
theorem continuous_negative_homogeneous_zero (f : (Fin N → ℝ) → ℝ)
    (hf : Continuous f) (β : ℝ) (hβ : 0 < β)
    (h : ∀ t, 0 < t → ∀ x, f x = t ^ β * f (G.dilate t x)) : f = 0 := by
  funext x
  let s : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  have hs : Tendsto s atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hspos : ∀ n, 0 < s n := fun n => pow_pos (by norm_num) n
  have hD : Tendsto (fun n => G.dilate (s n) x) atTop (𝓝 0) := by
    convert (continuousAt_dilate_parameter_zero G x).tendsto.comp hs using 1
    · funext n
      rfl
    · rw [zero_dilate G x]
  have hp : Tendsto (fun n => (s n) ^ β) atTop (𝓝 0) := by
    convert (Real.continuousAt_rpow_const 0 β (Or.inr (le_of_lt hβ))).tendsto.comp hs using 1
    · congr 1
    · rw [Real.zero_rpow (ne_of_gt hβ)]
  have hz := hp.mul (hf.continuousAt.tendsto.comp hD)
  have he : (fun n => (s n) ^ β * f (G.dilate (s n) x)) = fun _ : ℕ => f x := by
    funext n
    exact (h (s n) (hspos n) x).symm
  dsimp only [Function.comp_apply] at hz
  rw [he] at hz
  simpa using tendsto_nhds_unique tendsto_const_nhds hz

end RothschildStein.G2

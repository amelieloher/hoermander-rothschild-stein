-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.GaugeConsequences
public import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open RothschildStein.G2

/-- The fixed radial cutoff (BB Lemma 8.24, pp. 354–356). -/
def radialCutoff (t : ℝ) : ℝ := min 1 (max 0 (2 - t))

/-- The cutoff takes values in the unit interval. -/
theorem radialCutoff_bounds (t : ℝ) : 0 ≤ radialCutoff t ∧ radialCutoff t ≤ 1 := by
  constructor
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

/-- The cutoff equals one up to radius one. -/
theorem radialCutoff_eq_one {t : ℝ} (ht : t ≤ 1) : radialCutoff t = 1 := by
  unfold radialCutoff
  apply min_eq_left
  exact le_trans (by linarith : (1 : ℝ) ≤ 2 - t) (le_max_right _ _)

/-- The cutoff vanishes at radius two and beyond. -/
theorem radialCutoff_eq_zero {t : ℝ} (ht : 2 ≤ t) : radialCutoff t = 0 := by
  unfold radialCutoff
  rw [max_eq_left (by linarith)]
  norm_num

/-- The explicit cutoff has Lipschitz constant one. -/
theorem radialCutoff_lipschitz : LipschitzWith 1 radialCutoff := by
  have h : LipschitzWith 1 (fun t : ℝ => 2 - t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    have he : 2 - x - (2 - y) = -(x - y) := by ring
    rw [he, abs_neg]
  exact (h.const_max 0).const_min 1

/-- The truncated kernel uses the fixed group product and inverse. -/
def truncatedKernel {N : ℕ} (G : HomogeneousGroup N)
    (ν f : (Fin N → ℝ) → ℝ) (x y : Fin N → ℝ) : ℝ :=
  f (G.mul (G.inv y) x) * radialCutoff (gaugeDistance G ν x y)

/-- Support includes the endpoint required by Data D. -/
theorem truncatedKernel_eq_zero {N : ℕ} (G : HomogeneousGroup N)
    (ν f : (Fin N → ℝ) → ℝ) (x y : Fin N → ℝ)
    (h : 2 ≤ gaugeDistance G ν x y) : truncatedKernel G ν f x y = 0 := by
  unfold truncatedKernel
  rw [radialCutoff_eq_zero h]
  ring

/-- Transposition reflects the kernel in the group inverse. -/
theorem truncatedKernel_transpose {N : ℕ} (G : HomogeneousGroup N)
    (ν : HomogeneousNorm G) (hν : ν.Symmetric)
    (f : (Fin N → ℝ) → ℝ) (x y : Fin N → ℝ) :
    truncatedKernel G ν f y x =
      truncatedKernel G ν (fun w => f (G.inv w)) x y := by
  unfold truncatedKernel
  rw [gaugeDistance_symmetric G ν hν x y]
  dsimp only
  rw [inv_product, inv_inv]

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Metric

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X]

/-- The clamped distance cutoff of BB Lemma 7.7, printed p. 298. -/
def ballCutoff (x₀ : X) (r R : ℝ) (x : X) : ℝ :=
  min 1 (max 0 ((R - dist x₀ x) / (R - r)))

/-- The cutoff takes values in the unit interval. -/
theorem ballCutoff_bounds (x₀ : X) (r R : ℝ) (x : X) :
    0 ≤ ballCutoff x₀ r R x ∧ ballCutoff x₀ r R x ≤ 1 := by
  exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

/-- The cutoff equals one on the inner closed ball. -/
theorem ballCutoff_eq_one {x₀ x : X} {r R : ℝ} (hrR : r < R)
    (hx : dist x x₀ ≤ r) : ballCutoff x₀ r R x = 1 := by
  unfold ballCutoff
  rw [min_eq_left]
  apply le_trans _ (le_max_right _ _)
  apply (le_div_iff₀ (sub_pos.mpr hrR)).mpr
  rw [dist_comm x₀ x]
  linarith

/-- The cutoff vanishes outside the outer open ball. -/
theorem ballCutoff_eq_zero {x₀ x : X} {r R : ℝ} (hrR : r < R)
    (hx : R ≤ dist x x₀) : ballCutoff x₀ r R x = 0 := by
  unfold ballCutoff
  rw [max_eq_left, min_eq_right (by norm_num)]
  apply div_nonpos_of_nonpos_of_nonneg
  · rw [dist_comm x₀ x]; linarith
  · exact (sub_pos.mpr hrR).le

/-- The exact Lipschitz constant is the reciprocal radius gap. -/
theorem ballCutoff_lipschitz {x₀ : X} {r R : ℝ} (hrR : r < R) :
    LipschitzWith (Real.toNNReal ((R - r)⁻¹))
      (ballCutoff x₀ r R) := by
  have ha : LipschitzWith (Real.toNNReal ((R - r)⁻¹))
      (fun x : X => (R - dist x₀ x) / (R - r)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have hd : |dist x₀ x - dist x₀ y| ≤ dist x y := by
      simpa [dist_comm] using abs_dist_sub_le x y x₀
    have he : (R - dist x₀ x) / (R - r) - (R - dist x₀ y) / (R - r) =
        -(dist x₀ x - dist x₀ y) / (R - r) := by ring
    rw [he, abs_div, abs_neg, abs_of_pos (sub_pos.mpr hrR)]
    simp only [Real.coe_toNNReal', max_eq_left (inv_nonneg.mpr (sub_pos.mpr hrR).le)]
    change |dist x₀ x - dist x₀ y| / (R - r) ≤ (R - r)⁻¹ * dist x y
    rw [div_eq_mul_inv, mul_comm (R - r)⁻¹]
    exact mul_le_mul_of_nonneg_right hd (inv_nonneg.mpr (sub_pos.mpr hrR).le)
  exact (ha.const_max 0).const_min 1

end RothschildStein.H2

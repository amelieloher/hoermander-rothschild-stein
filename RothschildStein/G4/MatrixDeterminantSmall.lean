-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.MatrixInverseBound
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Metric
open scoped Topology Matrix.Norms.Elementwise

namespace RothschildStein.G4

/-- There is a dimension-only positive entry threshold making both
normalized inverse and determinant estimates valid. Compact coefficient-family
data are not needed for this purely matrix threshold
(BB Prop 9.50 and Lemma 9.51, pp. 445–447). -/
theorem exists_matrix_perturbation_threshold (n : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ (n : ℝ) * κ ≤ 1 / 4 ∧
      ∀ M : Matrix (Fin n) (Fin n) ℝ, (∀ i j, |M i j| ≤ κ) →
        |Matrix.det (1 + M) - 1| < 1 / 2 := by
  have hc : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => Matrix.det (1 + M)) :=
    (continuous_const.add continuous_id).matrix_det
  obtain ⟨ε, hε, hbound⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := 0)) (1 / 2) (by norm_num)
  let κ := min (ε / 2) (1 / (4 * ((n : ℝ) + 1)))
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  refine ⟨κ, hκ, ?_, ?_⟩
  · have h := (le_div_iff₀ (show 0 < 4 * ((n : ℝ) + 1) by positivity)).mp
      (min_le_right (ε / 2) (1 / (4 * ((n : ℝ) + 1))))
    change κ * (4 * ((n : ℝ) + 1)) ≤ 1 at h
    nlinarith
  · intro M hM
    have hnorm : ‖M‖ ≤ κ := by
      apply (pi_norm_le_iff_of_nonneg hκ.le).mpr
      intro i
      exact (pi_norm_le_iff_of_nonneg hκ.le).mpr (fun j => by simpa only [Real.norm_eq_abs] using hM i j)
    have he : dist M 0 < ε := by
      rw [dist_zero_right]
      exact hnorm.trans_lt ((min_le_left _ _).trans_lt (by linarith))
    have h := hbound he
    simpa only [add_zero, Matrix.det_one, Real.dist_eq, sub_zero] using h

end RothschildStein.G4

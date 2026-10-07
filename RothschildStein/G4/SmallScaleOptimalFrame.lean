-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.Suboptimality

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- A finite weighted family has one nonzero index optimal at
all sufficiently small radii: first minimize weight, then maximize the
coefficient among that weight (BB (9.52)–(9.53), p. 453). -/
theorem exists_eventually_optimal_weighted_index {ι : Type*} [Fintype ι]
    (coeff : ι → ℝ) (W : ι → ℤ) (hspan : ∃ J, coeff J ≠ 0) :
    ∃ B, coeff B ≠ 0 ∧ ∃ R : ℝ, 0 < R ∧ R ≤ 1 ∧
      ∀ r : ℝ, 0 < r → r ≤ R → ∀ J,
        |coeff J| * r ^ W J ≤ |coeff B| * r ^ W B := by
  classical
  obtain ⟨J₀, hJ₀⟩ := hspan
  let S := Finset.univ.filter (fun J => coeff J ≠ 0)
  have hS : S.Nonempty := ⟨J₀, by simp [S, hJ₀]⟩
  obtain ⟨A, hA, hmin⟩ := Finset.exists_min_image S W hS
  let T := S.filter (fun J => W J = W A)
  have hT : T.Nonempty := ⟨A, by simp [T, hA]⟩
  obtain ⟨B, hB, hmax⟩ := Finset.exists_max_image T (fun J => |coeff J|) hT
  have hBS : B ∈ S := (Finset.mem_filter.mp hB).1
  have hBW : W B = W A := (Finset.mem_filter.mp hB).2
  have hBcoeff : coeff B ≠ 0 := (Finset.mem_filter.mp hBS).2
  let C := ∑ J, |coeff J|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hCJ : ∀ J, |coeff J| ≤ C := by
    intro J
    change |coeff J| ≤ ∑ K, |coeff K|
    exact Finset.single_le_sum (f := fun K => |coeff K|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ J)
  let R := min 1 (|coeff B| / (C + 1))
  have hR : 0 < R := lt_min zero_lt_one (div_pos (abs_pos.mpr hBcoeff) (by linarith))
  refine ⟨B, hBcoeff, R, hR, min_le_left _ _, ?_⟩
  intro r hr hrR J
  have hr1 : r ≤ 1 := hrR.trans (min_le_left _ _)
  have hrbound : r * (C + 1) ≤ |coeff B| :=
    (le_div_iff₀ (show 0 < C + 1 by linarith)).mp (hrR.trans (min_le_right _ _))
  by_cases hJ : coeff J = 0
  · simp only [hJ, abs_zero, zero_mul]
    exact mul_nonneg (abs_nonneg _) (zpow_nonneg hr.le _)
  have hJW : W B ≤ W J := by
    rw [hBW]
    exact hmin J (by simp [S, hJ])
  by_cases hEq : W J = W B
  · have hJT : J ∈ T := by simp [T, S, hJ, hEq, hBW]
    rw [hEq]
    exact mul_le_mul_of_nonneg_right (hmax J hJT) (zpow_nonneg hr.le _)
  have hgap : (1 : ℤ) ≤ W J - W B := by omega
  have hpow : r ^ (W J - W B) ≤ r := by
    simpa only [zpow_one] using zpow_le_zpow_right_of_le_one₀ hr hr1 hgap
  have hcoef : |coeff J| * r ^ (W J - W B) ≤ |coeff B| := by
    calc
      _ ≤ |coeff J| * r := mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
      _ ≤ C * r := mul_le_mul_of_nonneg_right (hCJ J) hr.le
      _ ≤ |coeff B| := by nlinarith
  calc
    |coeff J| * r ^ W J = |coeff J| * (r ^ (W J - W B) * r ^ W B) := by
      rw [← zpow_add₀ hr.ne', sub_add_cancel]
    _ = (|coeff J| * r ^ (W J - W B)) * r ^ W B := by ring
    _ ≤ |coeff B| * r ^ W B := mul_le_mul_of_nonneg_right hcoef (zpow_nonneg hr.le _)

/-- The reference frame is optimal at every sufficiently small
radius at the fixed point; no neighboring-point vanishing is used
(BB (9.52)–(9.53), p. 453). -/
theorem exists_small_scale_optimal_frame {ι : Type*} [Fintype ι] {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+) (x : Fin n → ℝ)
    (hspan : ∃ B : Fin n → ι, frameDet Z B x ≠ 0) :
    ∃ B : Fin n → ι, frameDet Z B x ≠ 0 ∧ ∃ R : ℝ, 0 < R ∧ R ≤ 1 ∧
      ∀ r : ℝ, 0 < r → r ≤ R → IsSuboptimal Z w B x 1 r := by
  obtain ⟨B, hB, R, hR, hR1, hmax⟩ := exists_eventually_optimal_weighted_index
    (fun B : Fin n → ι => frameDet Z B x) (frameWeight w) hspan
  refine ⟨B, hB, R, hR, hR1, ?_⟩
  intro r hr hrR C
  simpa only [one_mul] using hmax r hr hrR C

end RothschildStein.G4

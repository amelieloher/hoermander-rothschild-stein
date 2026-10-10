-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Summing positive radii under uniform dyadic-band counting bounds. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace HeatKernel

/-- Every positive radius below M belongs to a successive pair of halving scales. -/
theorem exists_dyadic_radius_band {a M : ℝ} (ha : 0 < a) (hM : 0 < M) (haM : a ≤ M) :
    ∃ n : ℕ, M * (1 / 2 : ℝ) ^ (n + 1) < a ∧ a ≤ M * (1 / 2 : ℝ) ^ n := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one (div_pos ha hM)
    ((div_le_one hM).mpr haM) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, ?_, ?_⟩
  · have := (lt_div_iff₀ hM).mp hn
    nlinarith
  · have := (div_le_iff₀ hM).mp hn'
    nlinarith

/-- A finite family assigned to dyadic bands with at most P members in each band has
sum of radii at most 2PM. -/
theorem sum_le_of_dyadic_radius_assignment {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (n : ι → ℕ) {M P : ℝ} (hM : 0 ≤ M) (hP : 0 ≤ P)
    (hupper : ∀ i ∈ s, a i ≤ M * (1 / 2 : ℝ) ^ n i)
    (hcount : ∀ k : ℕ, ((s.filter fun i => n i = k).card : ℝ) ≤ P) :
    (∑ i ∈ s, a i) ≤ 2 * P * M := by
  classical
  let t := s.image n
  have hgeo : (∑ k ∈ t, (1 / 2 : ℝ) ^ k) ≤ 2 := by
    have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    have ht := hs.sum_le_tsum t (fun _ _ => pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _)
    have he : (∑' k : ℕ, (1 / 2 : ℝ) ^ k) = 2 := by
      rw [tsum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)]
      norm_num
    exact ht.trans_eq he
  calc
    (∑ i ∈ s, a i) = ∑ k ∈ t, ∑ i ∈ s with n i = k, a i :=
      (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem n hi) a).symm
    _ ≤ ∑ k ∈ t, P * (M * (1 / 2 : ℝ) ^ k) := by
      apply Finset.sum_le_sum
      intro k _
      calc
        (∑ i ∈ s with n i = k, a i) ≤
            ∑ _i ∈ s with n _i = k, M * (1 / 2 : ℝ) ^ k := by
          apply Finset.sum_le_sum
          intro i hi
          obtain ⟨his, hik⟩ := Finset.mem_filter.mp hi
          simpa only [hik] using hupper i his
        _ = ((s.filter fun i => n i = k).card : ℝ) * (M * (1 / 2 : ℝ) ^ k) := by
          simp [nsmul_eq_mul]
        _ ≤ P * (M * (1 / 2 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_right (hcount k) (mul_nonneg hM (pow_nonneg (by norm_num) _))
    _ = (P * M) * ∑ k ∈ t, (1 / 2 : ℝ) ^ k := by
      simp only [← mul_assoc, Finset.mul_sum]
    _ ≤ (P * M) * 2 := mul_le_mul_of_nonneg_left hgeo (mul_nonneg hP hM)
    _ = 2 * P * M := by ring

end HeatKernel

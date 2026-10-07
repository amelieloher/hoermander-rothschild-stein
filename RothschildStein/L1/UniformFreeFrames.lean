-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CompactFrameBounds
public import RothschildStein.G4.Suboptimality

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.L1

/-- Fixed-weight free frames are uniformly suboptimal at every
positive radius on a compact patch (BB pp. 514–516, Proposition 10.35). -/
theorem exists_uniform_free_frame_suboptimality {ι : Type*} [Fintype ι] {n : ℕ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+)
    (hZ : ∀ i, ContinuousOn (Z i) K) (F : Finset (Fin n → ι)) (Q : ℤ)
    (hnonzero : ∀ B ∈ F, ∀ x ∈ K, G4.frameDet Z B x ≠ 0)
    (hzero : ∀ B, B ∉ F → ∀ x ∈ K, G4.frameDet Z B x = 0)
    (hweight : ∀ B ∈ F, G4.frameWeight w B = Q) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ ∀ x ∈ K, ∀ B ∈ F, ∀ r : ℝ, 0 < r →
      G4.IsSuboptimal Z w B x t r := by
  classical
  obtain ⟨a, b, ha, hb, hupper, hlower⟩ := exists_compact_frame_bounds hK Z hZ F hnonzero
  let t := min 1 (a / b)
  have ht : 0 < t := lt_min zero_lt_one (div_pos ha hb)
  have htb : t * b ≤ a := (le_div_iff₀ hb).mp (min_le_right _ _)
  refine ⟨t, ht, min_le_left _ _, ?_⟩
  intro x hx B hB r hr C
  by_cases hC : C ∈ F
  · rw [hweight C hC, hweight B hB]
    have hh : t * |G4.frameDet Z C x| ≤ |G4.frameDet Z B x| :=
      (mul_le_mul_of_nonneg_left (hupper C x hx) ht.le).trans
        (htb.trans (hlower B hB x hx))
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (zpow_nonneg hr.le Q)
  · rw [hzero C hC x hx, abs_zero, zero_mul, mul_zero]
    exact mul_nonneg (abs_nonneg _) (zpow_nonneg hr.le _)

end RothschildStein.L1

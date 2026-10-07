-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.GaugeBalls

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.G2
variable {N : ℕ} {G : HomogeneousGroup N}

private theorem scalar_root_comparison {a R e d : ℝ}
    (ha : 0 ≤ a) (haR : a ≤ R) (hR : 1 ≤ R)
    (hd : 0 < d) (hde : d ≤ e) (he : e ≤ 1) :
    a ≤ R * a ^ e ∧ a ^ e ≤ R * a ^ d := by
  have factor : ∀ q : ℝ, 0 ≤ q → q ≤ 1 → a ^ q ≤ R := by
    intro q hq hq1
    by_cases ha1 : a ≤ 1
    · exact (Real.rpow_le_one ha ha1 hq).trans hR
    · exact (Real.rpow_le_self_of_one_le (le_of_not_ge ha1) hq1).trans haR
  have hf1 := factor (1 - e) (sub_nonneg.mpr he) (by linarith)
  have hf2 := factor (e - d) (sub_nonneg.mpr hde) (by linarith)
  constructor
  · calc
      a = a ^ (e + (1 - e)) := by rw [show e + (1 - e) = 1 by ring, Real.rpow_one]
      _ = a ^ e * a ^ (1 - e) := Real.rpow_add' ha (by ring_nf; norm_num)
      _ ≤ a ^ e * R := mul_le_mul_of_nonneg_left hf1 (Real.rpow_nonneg ha _)
      _ = R * a ^ e := mul_comm _ _
  · calc
      a ^ e = a ^ (d + (e - d)) := by congr 1; ring
      _ = a ^ d * a ^ (e - d) := Real.rpow_add' ha (by linarith)
      _ ≤ a ^ d * R := mul_le_mul_of_nonneg_left hf2 (Real.rpow_nonneg ha _)
      _ = R * a ^ d := mul_comm _ _

/-- The maximum coordinate weight is the last ordered weight
(BB Thm 3.12, pp. 101–102). -/
def maxWeight (G : HomogeneousGroup N) : ℕ := G.weight ⟨N - 1, by have := G.dimension_pos; omega⟩

private theorem weight_le_max (G : HomogeneousGroup N) (j : Fin N) :
    G.weight j ≤ maxWeight G := by
  unfold maxWeight
  apply G.weight_mono
  change j.val ≤ N - 1
  omega

private theorem maxWeight_pos (G : HomogeneousGroup N) : 0 < maxWeight G := G.weight_pos _

/-- Explicit comparison of the max gauge with the coordinate sup norm
on bounded sets (BB Thm 3.12, pp. 101–102; equivalent Euclidean norm). -/
theorem maxGauge_norm_comparison (G : HomogeneousGroup N) {R : ℝ} (hR : 1 ≤ R)
    {x : Fin N → ℝ} (hx : ‖x‖ ≤ R) :
    ‖x‖ ≤ R * rsGauge G.weight G.weight_pos x ∧
      rsGauge G.weight G.weight_pos x ≤ R * ‖x‖ ^ ((maxWeight G : ℝ)⁻¹) := by
  have hd : 0 < (maxWeight G : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr (maxWeight_pos G))
  have hb (j : Fin N) :
      |x j| ≤ R * |x j| ^ ((G.weight j : ℝ)⁻¹) ∧
      |x j| ^ ((G.weight j : ℝ)⁻¹) ≤ R * |x j| ^ ((maxWeight G : ℝ)⁻¹) := by
    apply scalar_root_comparison (abs_nonneg _) ((norm_le_pi_norm x j).trans hx) hR hd
    · exact inv_anti₀ (Nat.cast_pos.mpr (G.weight_pos j)) (Nat.cast_le.mpr (weight_le_max G j))
    · exact (inv_le_one₀ (Nat.cast_pos.mpr (G.weight_pos j))).mpr
        (by exact_mod_cast G.weight_pos j)
  constructor
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg (zero_le_one.trans hR) (gauge_nonneg G x))).mpr
    intro j
    exact (hb j).1.trans (mul_le_mul_of_nonneg_left
      (by simpa only [Real.rpow_eq_pow] using coordinate_root_le_gauge G x j) (zero_le_one.trans hR))
  · rw [gauge_le_iff]
    intro j
    simp only [Real.rpow_eq_pow]
    exact (hb j).2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) (norm_le_pi_norm x j) hd.le) (zero_le_one.trans hR))

/-- Every gauge has the local Euclidean comparison, with constants
chosen before the point (BB Thm 3.12, pp. 101–102). -/
theorem gauge_norm_comparison {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (R : ℝ) : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x : Fin N → ℝ, ‖x‖ ≤ R →
      a * ‖x‖ ≤ ν x ∧ ν x ≤ b * ‖x‖ ^ ((maxWeight G : ℝ)⁻¹) := by
  obtain ⟨a, b, ha, hb, hbounds⟩ := gauge_equivalent_max hν
  let R' := max 1 R
  have hR' : 0 < R' := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨a / R', b * R', div_pos ha hR', mul_pos hb hR', ?_⟩
  intro x hx
  have h := maxGauge_norm_comparison G (le_max_left 1 R) (hx.trans (le_max_right 1 R))
  constructor
  · have hn : ‖x‖ / R' ≤ rsGauge G.weight G.weight_pos x :=
      (div_le_iff₀ hR').mpr (by simpa [mul_comm] using h.1)
    calc
      a / R' * ‖x‖ = a * (‖x‖ / R') := by ring
      _ ≤ a * rsGauge G.weight G.weight_pos x := mul_le_mul_of_nonneg_left hn ha.le
      _ ≤ ν x := (hbounds x).1
  · calc
      ν x ≤ b * rsGauge G.weight G.weight_pos x := (hbounds x).2
      _ ≤ b * (R' * ‖x‖ ^ ((maxWeight G : ℝ)⁻¹)) := mul_le_mul_of_nonneg_left h.2 hb.le
      _ = b * R' * ‖x‖ ^ ((maxWeight G : ℝ)⁻¹) := (mul_assoc _ _ _).symm

/-- The same comparison holds on a gauge sublevel (BB Thm 3.12, p. 102). -/
theorem gauge_sublevel_norm_comparison {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (R : ℝ) : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x : Fin N → ℝ, ν x ≤ R →
      a * ‖x‖ ≤ ν x ∧ ν x ≤ b * ‖x‖ ^ ((maxWeight G : ℝ)⁻¹) := by
  obtain ⟨M, hM⟩ := (isCompact_gauge_le hν R).bddAbove_image continuous_norm.continuousOn
  obtain ⟨a, b, ha, hb, h⟩ := gauge_norm_comparison hν M
  exact ⟨a, b, ha, hb, fun x hx => h x (hM ⟨x, hx, rfl⟩)⟩

end RothschildStein.G2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import RothschildStein.Definitions.rsGauge
public import RothschildStein.Definitions.HomogeneousGroup.IsHomogeneousGauge

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G2

variable {N : ℕ} (G : HomogeneousGroup N)

private theorem coordinate_root_dilate (t : ℝ) (ht : 0 < t)
    (x : Fin N → ℝ) (j : Fin N) :
    Real.rpow |G.dilate t x j| ((G.weight j : ℝ)⁻¹) =
      t * Real.rpow |x j| ((G.weight j : ℝ)⁻¹) := by
  simp only [HomogeneousGroup.dilate, coordinateDilation, abs_mul,
    abs_of_pos (pow_pos ht _), Real.rpow_eq_pow]
  rw [Real.mul_rpow (pow_nonneg ht.le _) (abs_nonneg _),
    Real.pow_rpow_inv_natCast ht.le (ne_of_gt (G.weight_pos j))]

private theorem gauge_eq_sup (x : Fin N → ℝ) :
    rsGauge G.weight G.weight_pos x =
      Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, G.dimension_pos⟩⟩)
        (fun j => Real.rpow |x j| ((G.weight j : ℝ)⁻¹)) := by
  rw [Finset.sup'_eq_csSup_image]
  simp [rsGauge]

/-- Each coordinate root is bounded by the max gauge (BB Prop 3.10, p. 100). -/
theorem coordinate_root_le_gauge (x : Fin N → ℝ) (j : Fin N) :
    Real.rpow |x j| ((G.weight j : ℝ)⁻¹) ≤ rsGauge G.weight G.weight_pos x := by
  rw [gauge_eq_sup]
  exact Finset.le_sup' (fun j : Fin N => Real.rpow |x j| ((G.weight j : ℝ)⁻¹)) (Finset.mem_univ j)

/-- The max gauge is the largest coordinate root (BB Prop 3.10, p. 100). -/
theorem gauge_le_iff (x : Fin N → ℝ) (r : ℝ) :
    rsGauge G.weight G.weight_pos x ≤ r ↔
      ∀ j, Real.rpow |x j| ((G.weight j : ℝ)⁻¹) ≤ r := by
  rw [gauge_eq_sup, Finset.sup'_le_iff]
  simp

/-- The max gauge is nonnegative (BB Prop 3.10, p. 100). -/
theorem gauge_nonneg (x : Fin N → ℝ) : 0 ≤ rsGauge G.weight G.weight_pos x := by
  exact (Real.rpow_nonneg (abs_nonneg _) _).trans
    (coordinate_root_le_gauge G x ⟨0, G.dimension_pos⟩)

/-- The max gauge vanishes precisely at zero (BB Prop 3.10, p. 100). -/
theorem gauge_eq_zero_iff (x : Fin N → ℝ) :
    rsGauge G.weight G.weight_pos x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext j
    have hroot : Real.rpow |x j| ((G.weight j : ℝ)⁻¹) = 0 :=
      le_antisymm (h ▸ coordinate_root_le_gauge G x j)
        (Real.rpow_nonneg (abs_nonneg _) _)
    have hw : (G.weight j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (G.weight_pos j))
    simpa using (Real.rpow_eq_zero (abs_nonneg _) (inv_ne_zero hw)).mp hroot
  · rintro rfl
    apply le_antisymm _ (gauge_nonneg G 0)
    rw [gauge_le_iff]
    intro j
    simp [Real.zero_rpow (inv_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt (G.weight_pos j))))]

/-- Continuity of the max gauge (BB Prop 3.10, pp. 100–101). -/
theorem continuous_gauge : Continuous (rsGauge G.weight G.weight_pos) := by
  change Continuous (fun x => rsGauge G.weight G.weight_pos x)
  simp_rw [gauge_eq_sup]
  apply Continuous.finset_sup'_apply
  intro j _
  exact (Real.continuous_rpow_const (inv_nonneg.mpr (Nat.cast_nonneg _))).comp
    (continuous_apply j).abs

/-- Degree one homogeneity of the max gauge (BB Prop 3.10, pp. 100–101). -/
theorem gauge_dilate (t : ℝ) (ht : 0 < t) (x : Fin N → ℝ) :
    rsGauge G.weight G.weight_pos (G.dilate t x) = t * rsGauge G.weight G.weight_pos x := by
  apply le_antisymm
  · rw [gauge_le_iff]
    intro j
    rw [coordinate_root_dilate G t ht]
    exact mul_le_mul_of_nonneg_left (coordinate_root_le_gauge G x j) ht.le
  · obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, G.dimension_pos⟩⟩)
      (fun j => Real.rpow |x j| ((G.weight j : ℝ)⁻¹))
    rw [gauge_eq_sup G x, hj, ← coordinate_root_dilate G t ht]
    exact coordinate_root_le_gauge G _ j

/-- The max gauge satisfies the gauge predicate (BB Prop 3.10). -/
theorem isHomogeneousGauge_max :
    G.IsHomogeneousGauge (rsGauge G.weight G.weight_pos) :=
  ⟨continuous_gauge G, gauge_nonneg G, gauge_eq_zero_iff G, gauge_dilate G⟩

/-- The coordinate max gauge is even (BB Prop 3.10, p. 100). -/
theorem gauge_neg (x : Fin N → ℝ) :
    rsGauge G.weight G.weight_pos (-x) = rsGauge G.weight G.weight_pos x := by
  simp [rsGauge]

/-- Max gauge sublevels are compact (BB Prop 3.9, pp. 99–100). -/
theorem isCompact_gauge_sublevel (r : ℝ) :
    IsCompact {x : Fin N → ℝ | rsGauge G.weight G.weight_pos x ≤ r} := by
  by_cases hr : 0 ≤ r
  · apply (isCompact_Icc : IsCompact (Icc (fun j : Fin N => -(r ^ G.weight j))
      (fun j : Fin N => r ^ G.weight j))).of_isClosed_subset
      (isClosed_le (continuous_gauge G) continuous_const)
    intro x hx
    constructor <;> intro j
    all_goals
      have h := (gauge_le_iff G x r).mp hx j
      have habs : |x j| ≤ r ^ G.weight j := by
        exact (Real.rpow_inv_le_iff_of_pos (abs_nonneg _) hr
          (Nat.cast_pos.mpr (G.weight_pos j))).mp (by simpa only [Real.rpow_eq_pow] using h) |>.trans_eq (Real.rpow_natCast _ _)
      first | exact (abs_le.mp habs).1 | exact (abs_le.mp habs).2
  · have he : {x : Fin N → ℝ | rsGauge G.weight G.weight_pos x ≤ r} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => hr ((gauge_nonneg G x).trans h)
    rw [he]
    exact isCompact_empty

end RothschildStein.G2

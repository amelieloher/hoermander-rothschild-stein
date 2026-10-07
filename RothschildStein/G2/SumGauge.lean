-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.QuasiBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Weighted sum root, for an arbitrary positive outer degree
(BB Prop 3.10, pp. 100–101). -/
def sumRootGauge (D : ℝ) (x : Fin N → ℝ) : ℝ :=
  (∑ j, |x j| ^ (D / (G.weight j : ℝ))) ^ D⁻¹

/-- The weighted sum root satisfies the homogeneous gauge predicate
(BB Prop 3.10, pp. 100–101). -/
theorem isHomogeneousGauge_sumRoot (D : ℝ) (hD : 0 < D) :
    G.IsHomogeneousGauge (sumRootGauge G D) := by
  have hw (j : Fin N) : 0 < (G.weight j : ℝ) := Nat.cast_pos.mpr (G.weight_pos j)
  have he (j : Fin N) : 0 < D / (G.weight j : ℝ) := div_pos hD (hw j)
  have hs (x : Fin N → ℝ) : 0 ≤ ∑ j, |x j| ^ (D / (G.weight j : ℝ)) :=
    Finset.sum_nonneg fun j _ => Real.rpow_nonneg (abs_nonneg _) _
  refine ⟨?_, fun x => Real.rpow_nonneg (hs x) _, ?_, ?_⟩
  · apply (Real.continuous_rpow_const (inv_pos.mpr hD).le).comp
    exact continuous_finsetSum _ fun j _ =>
      (Real.continuous_rpow_const (he j).le).comp (continuous_apply j).abs
  · intro x
    change (∑ j, |x j| ^ (D / (G.weight j : ℝ))) ^ D⁻¹ = 0 ↔ x = 0
    rw [Real.rpow_eq_zero (hs x) (inv_ne_zero hD.ne')]
    constructor
    · intro h
      ext j
      have hz : |x j| ^ (D / (G.weight j : ℝ)) = 0 := le_antisymm
        (h ▸ Finset.single_le_sum (f := fun k : Fin N => |x k| ^ (D / (G.weight k : ℝ))) (fun k _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ j))
        (Real.rpow_nonneg (abs_nonneg _) _)
      simpa using (Real.rpow_eq_zero (abs_nonneg _) (he j).ne').mp hz
    · rintro rfl
      apply Finset.sum_eq_zero
      intro j _
      simp [Real.zero_rpow (he j).ne']
  · intro t ht x
    have hterm (j : Fin N) : |G.dilate t x j| ^ (D / (G.weight j : ℝ)) =
        t ^ D * |x j| ^ (D / (G.weight j : ℝ)) := by
      simp only [HomogeneousGroup.dilate, coordinateDilation, abs_mul, abs_of_pos (pow_pos ht _)]
      rw [Real.mul_rpow (pow_nonneg ht.le _) (abs_nonneg _),
        ← Real.rpow_natCast_mul ht.le]
      congr 2
      field_simp [ne_of_gt (hw j)]
    unfold sumRootGauge
    simp_rw [hterm]
    rw [← Finset.mul_sum, Real.mul_rpow (Real.rpow_nonneg ht.le _) (hs x),
      Real.rpow_rpow_inv ht.le hD.ne']

/-- The weighted sum root is even; hence it is symmetric whenever the
inverse is reflection (BB Prop 3.10, p. 100). -/
theorem sumRootGauge_neg (D : ℝ) (x : Fin N → ℝ) :
    sumRootGauge G D (-x) = sumRootGauge G D x := by
  simp [sumRootGauge]

end RothschildStein.G2

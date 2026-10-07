-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.MappedShortFieldBudget

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- Repeated coefficient slots contribute their sum to the same
short field; this is the input required by the persistence theorem. -/
def aggregateMappedControls {ι σ : Type*} [Fintype ι] [DecidableEq σ]
    (I : ι → σ) (a : ι → ℝ) (J : σ) : ℝ :=
  ∑ i, if I i = J then a i else 0

/-- Aggregating repeated controls leaves the ACTUAL control field
unchanged, including the selected-plus-auxiliary family (BB p. 444). -/
theorem aggregateMappedControls_field_eq {ι σ : Type*} [Fintype ι] [Fintype σ]
    [DecidableEq σ] {n : ℕ} (I : ι → σ) (a : ι → ℝ)
    (Z : σ → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) :
    (∑ J, aggregateMappedControls I a J • Z J x) = ∑ i, a i • Z (I i) x := by
  simp only [aggregateMappedControls, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- Repeated slots enlarge the weighted control radius by at most
card(ι)+1. Positivity of each weight makes this one common factor valid
for every short-word weight. -/
theorem aggregateMappedControls_weighted_bound {ι σ : Type*} [Fintype ι]
    [DecidableEq σ] (I : ι → σ) (a : ι → ℝ) (w : σ → ℕ+)
    {e r : ℝ} (he : 0 ≤ e) (hr : 0 ≤ r)
    (ha : ∀ i, |a i| ≤ (e * r) ^ (w (I i) : ℕ)) (J : σ) :
    |aggregateMappedControls I a J| ≤
      (((Fintype.card ι : ℝ) + 1) * e * r) ^ (w J : ℕ) := by
  classical
  have hterm : ∀ i : ι, |if I i = J then a i else 0| ≤ (e * r) ^ (w J : ℕ) := by
    intro i
    split_ifs with hi
    · simpa only [hi] using ha i
    · exact (abs_zero.trans_le (pow_nonneg (mul_nonneg he hr) _))
  have hb : |aggregateMappedControls I a J| ≤
      (Fintype.card ι : ℝ) * (e * r) ^ (w J : ℕ) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact (Finset.sum_le_sum (fun i _ => hterm i)).trans_eq (by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])
  apply hb.trans
  have hc : (Fintype.card ι : ℝ) ≤ ((Fintype.card ι : ℝ) + 1) ^ (w J : ℕ) :=
    (by linarith : (Fintype.card ι : ℝ) ≤ (Fintype.card ι : ℝ) + 1).trans
      (le_self_pow₀ (by have hn := Nat.cast_nonneg (α := ℝ) (Fintype.card ι); linarith) (w J).ne_zero)
  have heq : (((Fintype.card ι : ℝ) + 1) * e * r) =
      ((Fintype.card ι : ℝ) + 1) * (e * r) := by ring
  conv_rhs => rw [heq, mul_pow]
  exact mul_le_mul_of_nonneg_right hc (pow_nonneg (mul_nonneg he hr) _)

end RothschildStein.G4

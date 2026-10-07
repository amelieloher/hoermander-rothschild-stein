-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderZeroOrder
public import RothschildStein.S.IntrinsicNormRepresentatives
public import RothschildStein.Definitions.holderXENorm
public import RothschildStein.Definitions.driftWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- The drift word family of order one contains precisely the
empty word and the horizontal singleton words. -/
theorem drift_wordFamily_one (q : ℕ) :
    wordFamily (driftWeight (q := q)) 1 =
      insert [] (Finset.univ.image (fun i : Fin q => [i.succ])) := by
  classical
  ext I
  rw [S.mem_wordFamily_iff, Finset.mem_insert, Finset.mem_image]
  constructor
  · intro hI
    have hl := (S.length_le_wordWeight (driftWeight (q := q)) I).trans hI
    cases I with
    | nil => exact Or.inl rfl
    | cons j J =>
      have hJ : J = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hl; omega)
      subst J
      have hj : j ≠ 0 := by
        intro hj
        subst j
        norm_num [wordWeight, driftWeight] at hI
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj
      exact Or.inr ⟨i, Finset.mem_univ i, rfl⟩
  · rintro (rfl | ⟨i, _, rfl⟩) <;> simp [wordWeight, driftWeight]

/-- The full fixed first-order norm is exactly the input
norm plus all horizontal first representative norms. The shared S
uniqueness theorem identifies the intrinsic infima. -/
theorem holderXENorm_drift_one_eq {N q : ℕ}
    (Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (U : Opens (Fin N → ℝ)) (α : ℝ) (u : (Fin N → ℝ) → ℝ)
    (jet : Fin q → (Fin N → ℝ) → ℝ)
    (hi : ∀ i, hasIntrinsicWordDeriv Y U [i.succ] u (jet i)) :
    holderXENorm driftWeight Y d U 1 α u =
      holderENorm d α (U : Set (Fin N → ℝ)) u +
        ∑ i : Fin q, holderENorm d α (U : Set (Fin N → ℝ)) (jet i) := by
  classical
  have hinj : Function.Injective (fun i : Fin q => [i.succ]) := by
    intro i j h
    exact Fin.succ_injective q (List.cons.inj h).1
  unfold holderXENorm
  rw [drift_wordFamily_one, Finset.sum_insert (by simp),
    Finset.sum_image (fun i _ j _ h => hinj h), S.intrinsicWordENorm_nil]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact S.intrinsicWordENorm_eq_representative U Y d [i.succ] α u (jet i) (hi i)

end RothschildStein.H3

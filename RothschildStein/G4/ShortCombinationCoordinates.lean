-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FormalShortCombination
public import RothschildStein.G4.AuxiliaryControl

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G4
open G3

/-- The actual finite-coordinate short-field sum is precisely
the finite Lie target used by the primitive approximation. -/
theorem finiteLieField_short_coordinate_combination {m n s : ℕ} {w : Fin m → ℕ+}
    (D : FreeModelData m s w) (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (a : Fin (Fintype.card (ShortWord w s)) → ℝ)
    {x : Fin n → ℝ} (hx : x ∈ Ω) :
    finiteLieField D X (normalizedWordTarget
      (shortWordCoefficients (fun I => a (Fintype.equivFin (ShortWord w s) I)))) x =
      ∑ j, a j • shortField w X (shortIndex w j) x := by
  rw [finiteLieField_short_combination D Ω X hX _ hx]
  exact Fintype.sum_equiv (Fintype.equivFin (ShortWord w s)) _ _
    (fun I => by simp only [shortIndex, Equiv.symm_apply_apply])

/-- Finite-coordinate constant-control budgets transfer to the
retained-word approximation budget without changing their weights. -/
theorem shortWordCoefficients_coordinate_weighted_bound {m s : ℕ} {w : Fin m → ℕ+}
    (a : Fin (Fintype.card (ShortWord w s)) → ℝ) (δ : ℝ)
    (ha : ∀ j, |a j| ≤ δ ^ (shortWeight w (shortIndex w j) : ℕ)) :
    ∀ I ∈ correctionWordEnumeration m s w s,
      |shortWordCoefficients (fun I => a (Fintype.equivFin (ShortWord w s) I)) I| ≤
        δ ^ wordWeight w I := by
  apply shortWordCoefficients_weighted_bound
  intro I
  simpa only [shortIndex, Equiv.symm_apply_apply] using
    ha (Fintype.equivFin (ShortWord w s) I)

end RothschildStein.G4

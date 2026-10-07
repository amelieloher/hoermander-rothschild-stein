-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.Frames
public import RothschildStein.G4.SelectedAuxiliaryFamily

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- Enumerating the short fields preserves the actual selected
frame matrix (BB Def 9.4 and Prop 9.52, pp. 402, 448). -/
theorem frameMatrix_reindex {ι σ : Type*} {n : ℕ} (e : ι ≃ σ)
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι) (x : Fin n → ℝ) :
    frameMatrix (fun J => Z (e.symm J)) (e ∘ B) x = frameMatrix Z B x := by
  ext i j
  apply sub_eq_zero.mp
  simp only [frameMatrix, Function.comp_apply, Equiv.symm_apply_apply, sub_self]

/-- Enumerating the fields preserves the actual determinant. -/
theorem frameDet_reindex {ι σ : Type*} {n : ℕ} (e : ι ≃ σ)
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι) (x : Fin n → ℝ) :
    frameDet (fun J => Z (e.symm J)) (e ∘ B) x = frameDet Z B x := by
  simp only [frameDet, frameMatrix_reindex]

/-- Enumerating the fields preserves actual Cramer coefficients
for every vector field, including the derivative-error field. -/
theorem frameCoefficient_reindex {ι σ : Type*} {n : ℕ} (e : ι ≃ σ)
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (i : Fin n) (x : Fin n → ℝ) :
    frameCoefficient (fun J => Z (e.symm J)) (e ∘ B) V i x =
      frameCoefficient Z B V i x := by
  simp only [frameCoefficient, replacementDet, frameDet, frameMatrix_reindex]

/-- The selected-plus-auxiliary family is exactly the combined
family over the enumerated short fields, with repeated slots retained
(BB Prop 9.52, p. 449). -/
theorem shortIndex_selectedAuxiliaryIndex {k n s : ℕ}
    (w : Fin k → ℕ+) (B : Fin n → ShortWord w s)
    (j : Fin (n + Fintype.card (ShortWord w s))) :
    shortIndex w (Fin.addCases ((Fintype.equivFin (ShortWord w s)) ∘ B) id j) =
      selectedAuxiliaryIndex w B j := by
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp [shortIndex, selectedAuxiliaryIndex]
  · intro i
    simp [shortIndex, selectedAuxiliaryIndex]

end RothschildStein.G4

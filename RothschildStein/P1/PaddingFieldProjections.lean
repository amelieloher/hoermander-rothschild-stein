-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingFieldDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.P1

/-- The projection of an extended field is the original field. -/
theorem paddingBaseCLM_baseField {n d : ℕ}
    (X : (Fin n → ℝ) → (Fin n → ℝ)) (ξ : Fin (n + d) → ℝ) :
    paddingBaseCLM n d (paddingBaseField (d := d) X ξ) = X (paddingBaseCLM n d ξ) :=
  paddingBaseCLM_join n d _ _

/-- Added diffusion fields project to the zero original direction. -/
theorem paddingBaseCLM_diffusionField {n d : ℕ}
    (j : Fin d) (ξ : Fin (n + d) → ℝ) :
    paddingBaseCLM n d (paddingDiffusionField (n := n) j ξ) = 0 := by
  ext i
  change (Pi.single (Fin.natAdd n j) (1 : ℝ) : Fin (n + d) → ℝ) (Fin.castAdd d i) = 0
  apply Pi.single_eq_of_ne
  intro h
  have he := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at he
  omega

/-- Added diffusion fields give the original coordinate basis
of the entire fiber; no added direction is left unspanned. -/
theorem paddingFiberCLM_diffusionField {n d : ℕ}
    (j : Fin d) (ξ : Fin (n + d) → ℝ) :
    paddingFiberCLM n d (paddingDiffusionField (n := n) j ξ) =
      Hormander.Interface.basisVec j := by
  ext i
  change (Pi.single (Fin.natAdd n j) (1 : ℝ) : Fin (n + d) → ℝ) (Fin.natAdd n i) =
    (Pi.single j (1 : ℝ) : Fin d → ℝ) i
  simp [Pi.single_apply, Fin.ext_iff]

end RothschildStein.P1

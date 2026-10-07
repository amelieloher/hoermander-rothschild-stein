-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingNoDriftControlDefs
public import RothschildStein.P1.PaddingFieldProjections
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.P1

/-- Projection of a padded control velocity removes the added
diffusions and preserves the actual original control coefficients. -/
theorem paddingBaseCLM_noDrift_control_sum {q n d : ℕ}
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (c : Fin (q + d) → ℝ) (ξ : Fin (n + d) → ℝ) :
    paddingBaseCLM n d (∑ i, c i • paddingNoDriftVectorFields X i ξ) =
      ∑ i : Fin q, c (Fin.castAdd d i) •
        X i (paddingBaseCLM n d ξ) := by
  rw [map_sum]
  simp_rw [map_smul]
  rw [Fin.sum_univ_add]
  simp [paddingNoDriftVectorFields_original, paddingNoDriftVectorFields_added,
    paddingBaseCLM_baseField, paddingBaseCLM_diffusionField]

/-- Lifting a control velocity with zero added controls is
exactly joining the original velocity with a zero added-coordinate block. -/
theorem paddingJoinCLM_noDrift_control_sum {q n d : ℕ}
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (a : Fin q → ℝ → ℝ) (t : ℝ) (x : Fin n → ℝ) (z : Fin d → ℝ) :
    (∑ i : Fin (q + d), paddingNoDriftControlCoefficients a i t •
      paddingNoDriftVectorFields X i (joinPoint x z)) =
        paddingJoinCLM n d (∑ i : Fin q, a i t • X i x, 0) := by
  have hp : paddingBaseCLM n d (paddingJoinCLM n d (x, z)) = x := by
    rw [paddingJoinCLM_apply, paddingBaseCLM_join]
  rw [Fin.sum_univ_add]
  simp [paddingNoDriftControlCoefficients, paddingNoDriftVectorFields_original, paddingNoDriftVectorFields_added, paddingBaseField,
    hp, ← paddingJoinCLM_apply, ← map_smul, ← map_sum]
  congr 1
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

end RothschildStein.P1

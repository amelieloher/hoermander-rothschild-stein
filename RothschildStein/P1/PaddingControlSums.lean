-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingControlDefs
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
theorem paddingBaseCLM_control_sum {q n d : ℕ}
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (c : Fin (q + d + 1) → ℝ) (ξ : Fin (n + d) → ℝ) :
    paddingBaseCLM n d (∑ i, c i • paddingVectorFields X i ξ) =
      ∑ i : Fin (q + 1), c (paddingGeneratorIndex (d := d) i) •
        X i (paddingBaseCLM n d ξ) := by
  rw [map_sum]
  simp_rw [map_smul]
  rw [Fin.sum_univ_succ, Fin.sum_univ_add, Fin.sum_univ_succ]
  simp [paddingVectorFields_zero, paddingVectorFields_original, paddingVectorFields_added,
    paddingBaseCLM_baseField, paddingBaseCLM_diffusionField, paddingGeneratorIndex]

/-- Lifting a control velocity with zero added controls is
exactly joining the original velocity with a zero added-coordinate block. -/
theorem paddingJoinCLM_control_sum {q n d : ℕ}
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (a : Fin (q + 1) → ℝ → ℝ) (t : ℝ) (x : Fin n → ℝ) (z : Fin d → ℝ) :
    (∑ i : Fin (q + d + 1), paddingControlCoefficients a i t •
      paddingVectorFields X i (joinPoint x z)) =
        paddingJoinCLM n d (∑ i : Fin (q + 1), a i t • X i x, 0) := by
  have hp : paddingBaseCLM n d (paddingJoinCLM n d (x, z)) = x := by
    rw [paddingJoinCLM_apply, paddingBaseCLM_join]
  rw [Fin.sum_univ_succ, Fin.sum_univ_add, Fin.sum_univ_succ]
  simp [paddingControlCoefficients, paddingVectorFields_zero,
    paddingVectorFields_original, paddingVectorFields_added, paddingBaseField,
    hp, ← paddingJoinCLM_apply, ← map_smul, ← map_sum, ← map_add]
  congr 1
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

end RothschildStein.P1

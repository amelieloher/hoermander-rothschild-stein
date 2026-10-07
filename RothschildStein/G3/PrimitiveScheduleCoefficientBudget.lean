-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RetainedLieListProducts
public import Mathlib.Data.Set.Finite.List
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G3

/-- Finite alphabet schedules of bounded length have one numerical coefficient
budget, including their BCH products, before any fields are selected. -/
theorem exists_primitiveSchedule_coefficient_budget {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (L : ℕ) :
    ∃ T : ℝ, 0 < T ∧
      (∀ b : Fin a × Bool, ‖D.basis.equivFun (primitiveScheduleLieInput b)‖ ≤ T) ∧
      ∀ S : List (Fin a × Bool), S.length ≤ L →
        ‖D.basis.equivFun (retainedLieListProduct (S.map primitiveScheduleLieInput))‖ ≤ T := by
  let f := fun S : List (Fin a × Bool) =>
    D.basis.equivFun (retainedLieListProduct (S.map primitiveScheduleLieInput))
  obtain ⟨C,hC⟩ := ((List.finite_length_le (Fin a × Bool) L).image f).isCompact.isBounded.exists_norm_le
  let A := ∑ b : Fin a × Bool, ‖D.basis.equivFun (primitiveScheduleLieInput b)‖
  have hA : 0 ≤ A := Finset.sum_nonneg (fun b _ => norm_nonneg _)
  refine ⟨1+|C|+A,by positivity,?_,?_⟩
  · intro b
    have he : ‖D.basis.equivFun (primitiveScheduleLieInput b)‖ ≤ A :=
      by
        dsimp only [A]
        exact Finset.single_le_sum
          (fun j (_ : j ∈ Finset.univ) => norm_nonneg (D.basis.equivFun (primitiveScheduleLieInput j)))
          (Finset.mem_univ b)
    linarith [abs_nonneg C]
  · intro S hS
    have he := hC (f S) (mem_image_of_mem f hS)
    exact ((he.trans (le_abs_self C)).trans (by linarith))
end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.TimedPrimitiveLieInputs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Finite-dimensional coefficient coordinates as a bounded linear map. -/
def retainedCoefficientMap {a s : ℕ} {p : Fin a → ℕ+} (D : FreeModelData a s p) :
    formalSpan a s p →L[ℝ] (Fin (freeDimension a s p) → ℝ) :=
  D.basis.equivFun.toLinearMap.toContinuousLinearMap

/-- Normalized real times and normalized target coefficients share one
numerical coordinate budget, selected without any fields. -/
theorem exists_timedPrimitive_coefficient_budget {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) {A R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) :
    ∃ T : ℝ, 0 < T ∧
      (∀ b : Fin a × ℝ, |b.2| ≤ A → ‖D.basis.equivFun (timedPrimitiveLieInput b)‖ ≤ T) ∧
      ∀ f : formalSpan a s p, ‖f‖ ≤ R → ‖D.basis.equivFun f‖ ≤ T := by
  let C := 1+∑ i : Fin a, ‖D.basis.equivFun (wordLieElement [i])‖
  have hC : 0 < C := by dsimp [C]; positivity
  let T := 1+A*C+‖retainedCoefficientMap D‖*R
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨T,hT,?_,?_⟩
  · intro b hb
    have hi : ‖D.basis.equivFun (wordLieElement [b.1])‖ ≤ C := by
      have he := Finset.single_le_sum
        (fun j (_ : j ∈ Finset.univ) => norm_nonneg (D.basis.equivFun (wordLieElement [j])))
        (Finset.mem_univ b.1)
      change ‖D.basis.equivFun (wordLieElement [b.1])‖ ≤
        1 + ∑ i : Fin a, ‖D.basis.equivFun (wordLieElement [i])‖
      exact he.trans (le_add_of_nonneg_left zero_le_one)
    calc
      ‖D.basis.equivFun (timedPrimitiveLieInput b)‖ =
          |b.2| * ‖D.basis.equivFun (wordLieElement [b.1])‖ := by
        rw [timedPrimitiveLieInput, map_smul, norm_smul, Real.norm_eq_abs]
      _ ≤ A * C := mul_le_mul hb hi (norm_nonneg _) hA
      _ ≤ T := by
        change A * C ≤ 1 + A * C + ‖retainedCoefficientMap D‖ * R
        linarith [mul_nonneg (norm_nonneg (retainedCoefficientMap D)) hR]
  · intro f hf
    have he := (retainedCoefficientMap D).le_opNorm f
    have he' : ‖D.basis.equivFun f‖ ≤ ‖retainedCoefficientMap D‖*R :=
      he.trans (mul_le_mul_of_nonneg_left hf (norm_nonneg _))
    apply he'.trans
    change ‖retainedCoefficientMap D‖ * R ≤ 1 + A * C + ‖retainedCoefficientMap D‖ * R
    linarith [mul_nonneg hA hC.le]
end RothschildStein.G3

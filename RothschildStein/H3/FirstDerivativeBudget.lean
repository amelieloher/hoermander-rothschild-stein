-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.EuclideanDerivativeBounds
public import RothschildStein.H3.KernelDerivativeProperties

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.H3
variable {N : ℕ}

/-- Every natural multiindex of budget one is zero or a
single order-one coordinate, including all coordinates in the finite maximum. -/
theorem multiindex_budget_one_cases (a : Fin N → ℕ) (ha : (∑ j, a j) ≤ 1) :
    a = (fun _ => 0) ∨ ∃ i : Fin N, a = Pi.single i 1 := by
  classical
  by_cases hz : ∀ j, a j = 0
  · exact Or.inl (funext hz)
  push Not at hz
  obtain ⟨i, hi⟩ := hz
  have hia : a i = 1 := by
    have hb := (Finset.single_le_sum (fun j _ => Nat.zero_le (a j))
      (Finset.mem_univ i)).trans ha
    omega
  refine Or.inr ⟨i, ?_⟩
  funext j
  by_cases hji : j = i
  · subst j; simpa only [Pi.single_eq_same] using hia
  · have hij : i ≠ j := fun h => hji h.symm
    have hs := Finset.sum_le_sum_of_subset (f := a)
      (Finset.subset_univ ({i, j} : Finset (Fin N)))
    have hab : a i + a j ≤ ∑ k : Fin N, a k := by
      simpa only [Finset.sum_pair hij] using hs
    have hj : a j = 0 := by omega
    simp only [hj, Pi.single_eq_of_ne hji]

/-- The budget-zero partial is the actual input function. -/
theorem euclideanPartial_zero (f : (Fin N → ℝ) → ℝ) :
    euclideanPartial (fun _ => 0) f = f := by
  have he : (List.finRange N).flatMap (fun j => List.replicate (0 : ℕ) j) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun j _ => by simp)
  simp only [euclideanPartial, he, List.foldr_nil]

/-- A coordinate differential is bounded by the actual
Euclidean differential norm because its Euclidean basis vector has norm one. -/
theorem coordinateDerivative_le_euclideanDifferential
    (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) (i : Fin N) :
    |fderiv ℝ f x (Hormander.Interface.basisVec i)| ≤ ‖euclideanDifferential f x‖ := by
  have he : coordinateEuclideanEquiv N (EuclideanSpace.basisFun (Fin N) ℝ i) =
      Hormander.Interface.basisVec i := by
    ext j
    simp [coordinateEuclideanEquiv, EuclideanSpace.basisFun_apply,
      Hormander.Interface.basisVec, Pi.single_apply]
  have hn : ‖EuclideanSpace.basisFun (Fin N) ℝ i‖ = 1 := by
    simp only [EuclideanSpace.basisFun_apply, PiLp.norm_single, norm_one]
  have hb := (euclideanDifferential f x).le_opNorm
    (EuclideanSpace.basisFun (Fin N) ℝ i)
  simpa only [euclideanDifferential, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, he, hn, mul_one, Real.norm_eq_abs] using hb

end RothschildStein.H3

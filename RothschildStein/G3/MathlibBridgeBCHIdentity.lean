-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G3.MathlibBridgeBCHLift
public import RothschildStein.G3.MathlibBridgeQuotient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Generators have zero augmentation (BB p. 468). -/
theorem mathlibGenerator_mem_augmentation {a : ℕ} (i : Fin a) :
    FreeAlgebra.ι ℚ i ∈ mathlibAugmentation a := by
  change FreeAlgebra.algebraMapInv (FreeAlgebra.ι ℚ i) = 0
  simp [FreeAlgebra.algebraMapInv]

/-- Positive homogeneous degrees have zero
augmentation (BB pp. 468–470). -/
theorem mathlibHomogeneous_mem_augmentation {a n : ℕ} {f : FreeAlgebra ℚ (Fin a)}
    (hn : n ≠ 0) (hf : f ∈
      Submodule.span ℚ (Set.range (FreeAlgebra.ι ℚ : Fin a → FreeAlgebra ℚ (Fin a))) ^ n) :
    f ∈ mathlibAugmentation a := by
  apply (mem_mathlibAugmentation_iff f).mpr
  exact mathlibCoefficients_homogeneous_of_generatorSpan_pow hf [] (by
    rw [ordinary_weight,List.length_nil]; exact Ne.symm hn)

/-- A finite positive-degree homogeneous sum
belongs to the augmentation ideal (BB p. 468). -/
theorem mathlibPartial_mem_augmentation (S : ℕ → FreeAlgebra ℚ (Fin 2))
    (hS : ∀ n, S n ∈ Submodule.span ℚ
      (Set.range (FreeAlgebra.ι ℚ : Fin 2 → FreeAlgebra ℚ (Fin 2))) ^ n) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, S n) ∈ mathlibAugmentation 2 := by
  apply Submodule.sum_mem
  intro n hn
  exact mathlibHomogeneous_mem_augmentation (by have := (Finset.mem_Icc.mp hn).1; omega) (hS n)

/-- The lifted BCH partial sum is precisely the
existing universal BCH truncation (BB pp. 470–472). -/
theorem mathlibBCHPartial_truncation (N : ℕ) :
    mathlibTruncation 2 N (∑ n ∈ Finset.Icc 1 N, mathlibLieImage 2 (mathlibBCHLift n)) =
      universalFiniteBCH N := by
  classical
  rw [map_sum]
  have ht : ∀ n, mathlibTruncation 2 N (mathlibLieImage 2 (mathlibBCHLift n)) =
      universalComponent N n := by
    intro n
    rw [universalComponent_eq]
    change ordinaryTrunc N (mathlibCoefficients 2 (mathlibLieImage 2 (mathlibBCHLift n))) = _
    rw [mathlibBCHLift_coefficients]
  simp_rw [ht]
  calc
    _ = ∑ n ∈ Finset.range (N+1), universalComponent N n := by
      apply Finset.sum_subset
      · intro n hn; simp only [Finset.mem_Icc,Finset.mem_range] at *; omega
      · intro n hn hnot
        have hz : n = 0 := by simp only [Finset.mem_Icc,Finset.mem_range] at *; omega
        subst n
        rw [universalComponent_eq,bchComponent_zero]
        rfl
    _ = _ := universalFiniteBCH_sum N

/-- The exact augmentation-quotient exponential
identity for the selected rational Lie components (BB Theorem 9.68, pp. 469–474). -/
theorem mathlibBCH_quotient_identity (N : ℕ) :
    IsNilpotent.exp (Ideal.Quotient.mk (mathlibAugmentation 2 ^ (N+1))
      (FreeAlgebra.ι ℚ (0 : Fin 2))) *
    IsNilpotent.exp (Ideal.Quotient.mk (mathlibAugmentation 2 ^ (N+1))
      (FreeAlgebra.ι ℚ (1 : Fin 2))) =
    IsNilpotent.exp (Ideal.Quotient.mk (mathlibAugmentation 2 ^ (N+1))
      (∑ n ∈ Finset.Icc 1 N, mathlibLieImage 2 (mathlibBCHLift n))) := by
  apply mathlibQuotientMap_injective N
  rw [map_mul,mathlibQuotientMap_exp N (mathlibGenerator_mem_augmentation 0),
    mathlibQuotientMap_exp N (mathlibGenerator_mem_augmentation 1),
    mathlibQuotientMap_exp N (mathlibPartial_mem_augmentation _
      (fun n => mathlibLieImage_mem_generatorSpan_pow (mathlibBCHLift_mem n)) N),
    mathlibBCHPartial_truncation,universalFiniteBCH_eq]
  have ht : ∀ i : Fin 2, mathlibTruncation 2 N (FreeAlgebra.ι ℚ i) =
      finiteLetter (a := 2) (s := N) (p := fun _ => 1) i := by
    intro i
    change ordinaryTrunc N (mathlibCoefficients 2 (FreeAlgebra.ι ℚ i)) = _
    rw [mathlibCoefficients_generator]
    rfl
  rw [ht,ht]
  exact (finiteExp_BCH (ordinaryTrunc_positive (letterSeries_positive 0) N)
    (ordinaryTrunc_positive (letterSeries_positive 1) N)).symm

end RothschildStein.G3

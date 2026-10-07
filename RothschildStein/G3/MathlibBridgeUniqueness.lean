-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G3.MathlibBridgeBCHIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Assembly of a homogeneous rational associative
series, coefficient by coefficient (BB Theorem 9.68, pp. 469–471). -/
def mathlibGradedAssembly (S : ℕ → FreeAlgebra ℚ (Fin 2)) : CoefficientSeries 2 :=
  fun I => mathlibCoefficients 2 (S I.length) I

/-- Positive partial sums agree with every truncation
of the assembled series, including the scalar quotient (BB pp. 468–471). -/
theorem mathlibGradedAssembly_truncation (S : ℕ → FreeAlgebra ℚ (Fin 2))
    (h0 : S 0 = 0) (hS : ∀ n, S n ∈ Submodule.span ℚ
      (Set.range (FreeAlgebra.ι ℚ : Fin 2 → FreeAlgebra ℚ (Fin 2))) ^ n) (N : ℕ) :
    mathlibTruncation 2 N (∑ n ∈ Finset.Icc 1 N, S n) =
      ordinaryTrunc N (mathlibGradedAssembly S) := by
  classical
  rw [map_sum]
  funext I
  change (∑ n ∈ Finset.Icc 1 N, mathlibTruncation 2 N (S n)) I = _
  rw [Finset.sum_apply]
  change (∑ n ∈ Finset.Icc 1 N, mathlibCoefficients 2 (S n) I.val) =
    mathlibCoefficients 2 (S I.val.length) I.val
  apply Finset.sum_eq_single I.val.length
  · intro n _ hn
    exact mathlibCoefficients_homogeneous_of_generatorSpan_pow (hS n) I.val
      (by rw [ordinary_weight]; exact Ne.symm hn)
  · intro hn
    have hlen := boundedWord_weight I
    change wordWeight (fun _ => 1) I.val ≤ N at hlen
    rw [ordinary_weight] at hlen
    have hz : I.val.length = 0 := by simp only [Finset.mem_Icc] at hn; omega
    rw [hz,h0,map_zero]
    rfl

/-- The fixed quotient identities force the
assembled series to be the unique formal BCH logarithm (BB pp. 469–471). -/
theorem mathlibBCH_associative_unique (S : ℕ → FreeAlgebra ℚ (Fin 2))
    (h0 : S 0 = 0) (hS : ∀ n, S n ∈ Submodule.span ℚ
      (Set.range (FreeAlgebra.ι ℚ : Fin 2 → FreeAlgebra ℚ (Fin 2))) ^ n)
    (he : ∀ N : ℕ,
      IsNilpotent.exp (Ideal.Quotient.mk (mathlibAugmentation 2 ^ (N+1))
        (FreeAlgebra.ι ℚ (0 : Fin 2))) *
      IsNilpotent.exp (Ideal.Quotient.mk (mathlibAugmentation 2 ^ (N+1))
        (FreeAlgebra.ι ℚ (1 : Fin 2))) =
      IsNilpotent.exp (Ideal.Quotient.mk (mathlibAugmentation 2 ^ (N+1))
        (∑ n ∈ Finset.Icc 1 N, S n))) :
    ∀ n, S n = mathlibLieImage 2 (mathlibBCHLift n) := by
  have hpos : PositiveSeries (mathlibGradedAssembly S) := by
    change mathlibCoefficients 2 (S 0) [] = 0
    rw [h0,map_zero]
    rfl
  have hexp : formalExp (mathlibGradedAssembly S) =
      formalExp (letterSeries 0) * formalExp (letterSeries 1) := by
    funext I
    have ht := congrArg (mathlibQuotientMap 2 I.length) (he I.length)
    rw [map_mul,mathlibQuotientMap_exp _ (mathlibGenerator_mem_augmentation 0),
      mathlibQuotientMap_exp _ (mathlibGenerator_mem_augmentation 1),
      mathlibQuotientMap_exp _ (mathlibPartial_mem_augmentation S hS I.length),
      mathlibGradedAssembly_truncation S h0 hS] at ht
    have hg : ∀ i : Fin 2, mathlibTruncation 2 I.length (FreeAlgebra.ι ℚ i) =
        ordinaryTrunc I.length (letterSeries i) := by
      intro i
      change ordinaryTrunc I.length (mathlibCoefficients 2 (FreeAlgebra.ι ℚ i)) = _
      rw [mathlibCoefficients_generator]
    rw [hg,hg] at ht
    have hx : ordinaryTrunc I.length (formalExp (mathlibGradedAssembly S)) =
        ordinaryTrunc I.length (formalExp (letterSeries 0) * formalExp (letterSeries 1)) := by
      rw [ordinaryTrunc_formalExp hpos,ordinaryTrunc_mul,
        ordinaryTrunc_formalExp (letterSeries_positive 0),
        ordinaryTrunc_formalExp (letterSeries_positive 1)]
      exact ht.symm
    exact congrFun hx (boundedWord (fun _ => 1) I (by rw [ordinary_weight]))
  have hb := formalBCH_unique (letterSeries_positive 0) (letterSeries_positive 1) hpos hexp
  intro n
  apply mathlibCoefficients_injective 2
  rw [mathlibBCHLift_coefficients]
  funext I
  by_cases hn : I.length = n
  · have hc := congrFun hb I
    change mathlibCoefficients 2 (S I.length) I = universalBCH I at hc
    rw [hn] at hc
    rw [hc]
    simp [bchComponent,homogeneousComponent,hn]
  · have hs := mathlibCoefficients_homogeneous_of_generatorSpan_pow (hS n) I
      (by rw [ordinary_weight]; exact hn)
    have hc := bchComponent_homogeneous n I (by rw [ordinary_weight]; exact hn)
    exact hs.trans hc.symm

end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RationalBCH
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The rational span of right-nested words of exactly one ordinary
length (BB Lemma 9.70, p. 472). -/
def homogeneousRationalLieSpan (a n : ℕ) : Submodule ℚ (CoefficientSeries a) :=
  Submodule.span ℚ {f | ∃ u : Nested (Fin a), u.letters.length = n ∧ f = u.eval letterSeries}

/-- A rational homogeneous Lie polynomial has a normal form with only
nested words of the same ordinary length (BB Lemma 9.70, p. 472). -/
theorem homogeneous_mem_rationalLieSpan {a n : ℕ} {f : CoefficientSeries a}
    (hf : f ∈ rationalSeriesLieAlgebra a) (hh : Homogeneous (fun _ => 1) n f) :
    f ∈ homogeneousRationalLieSpan a n := by
  let U : CoefficientSeries a →ₗ[ℚ] FiniteWordAlgebra a n (fun _ => 1) :=
    ((truncateSeries (a := a) (s := n) (p := fun _ => 1)).toLinearMap).restrictScalars ℚ
  let P : FiniteWordAlgebra a n (fun _ => 1) →ₗ[ℚ] FiniteWordAlgebra a n (fun _ => 1) :=
    (finiteWeightProjection n).restrictScalars ℚ
  let E : FiniteWordAlgebra a n (fun _ => 1) →ₗ[ℚ] CoefficientSeries a :=
    finiteExtendLinear.restrictScalars ℚ
  let T := E.comp (P.comp U)
  have ht : T f = f := by
    change (extend (weightProjection n (restrict f : WordCoefficients a n (fun _ => 1))) :
      CoefficientSeries a) = f
    have hp : weightProjection n (restrict f : WordCoefficients a n (fun _ => 1)) = restrict f := by
      funext J
      change (if wordWeight (fun _ => 1) J.val = n then f J.val else 0) = f J.val
      split
      · rfl
      · exact (hh J.val ‹_›).symm
    rw [hp]
    exact extend_restrict_eq_of_homogeneous hh le_rfl
  rw [← ht]
  clear ht hh
  rw [rationalSeriesLieAlgebra_eq_nested] at hf
  change f ∈ nestedWordSpan ℚ letterSeries at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨u, rfl⟩ := hg
    have he : T (u.eval letterSeries) =
        if u.letters.length = n then u.eval letterSeries else 0 := by
      change finiteExtendLinear (finiteWeightProjection n (truncateSeries (u.eval letterSeries))) = _
      have hu : truncateSeries (s := n) (p := fun _ => 1) (u.eval letterSeries) = u.eval finiteLetter := by
        rw [nested_eval_formalBracket, nested_eval_truncatedBracket]
        rfl
      rw [hu, finiteWeightProjection_nested, ordinary_weight]
      split
      · rw [finiteExtendLinear_nested, ordinary_weight, ite_eq_left (by omega)]
      · exact (finiteExtendLinear (a := a) (s := n) (p := fun _ => 1)).map_zero
    rw [he]
    split
    · exact Submodule.subset_span ⟨u, ‹_›, rfl⟩
    · exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul r f _ hf => rw [map_smul]; exact Submodule.smul_mem _ r hf

/-- Every degree-n BCH coefficient is a rational linear combination
of n-letter nested commutators (BB Lemma 9.70, pp. 471–474). -/
theorem bchComponent_mem_homogeneousRationalLieSpan (n : ℕ) :
    bchComponent n ∈ homogeneousRationalLieSpan 2 n :=
  homogeneous_mem_rationalLieSpan (bchComponent_mem_rationalSeriesLieAlgebra n)
    (bchComponent_homogeneous n)
end RothschildStein.G3

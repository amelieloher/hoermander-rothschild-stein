-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RationalLieAlgebras
public import RothschildStein.G3.Grading
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Weighted coefficient projection as a linear map on the
associative finite carrier (BB Lemma 9.70, p. 472; Proposition 10.42, p. 524). -/
def finiteWeightProjection {a s : ℕ} {p : Fin a → ℕ+} (k : ℕ) :
    FiniteWordAlgebra a s p →ₗ[ℝ] FiniteWordAlgebra a s p where
  toFun := weightProjection k
  map_add' f g := (weightProjection k).map_add f g
  map_smul' r f := (weightProjection k).map_smul r f

/-- Projection selects the weight of a nested word (BB p. 524). -/
theorem finiteWeightProjection_nested {a s : ℕ} {p : Fin a → ℕ+}
    (k : ℕ) (u : Nested (Fin a)) :
    finiteWeightProjection k (u.eval (finiteLetter (s := s) (p := p))) =
      if wordWeight p u.letters = k then u.eval finiteLetter else 0 := by
  rw [nested_eval_truncatedBracket]
  change (weightProjection k (truncatedBracket u.letters) : WordCoefficients a s p) =
    if wordWeight p u.letters = k then truncatedBracket u.letters else 0
  exact weightProjection_truncatedBracket k u.letters

/-- Homogeneous components of rational Lie polynomials are rational Lie
polynomials (BB Lemma 9.70, p. 472). -/
theorem finiteWeightProjection_mem_rationalLieAlgebra {a s : ℕ} {p : Fin a → ℕ+}
    (k : ℕ) {f : FiniteWordAlgebra a s p} (hf : f ∈ rationalCoefficientLieAlgebra a s p) :
    finiteWeightProjection k f ∈ rationalCoefficientLieAlgebra a s p := by
  rw [rationalCoefficientLieAlgebra_eq_nested] at hf ⊢
  let P := (finiteWeightProjection (a := a) (s := s) (p := p) k).restrictScalars ℚ
  change P f ∈ nestedWordSpan ℚ finiteLetter
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨u, rfl⟩ := hg
    change finiteWeightProjection k (u.eval finiteLetter) ∈ _
    rw [finiteWeightProjection_nested]
    split
    · exact Submodule.subset_span ⟨u, rfl⟩
    · exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using (nestedWordSpan ℚ finiteLetter).zero_mem
  | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul r f _ hf => rw [map_smul]; exact Submodule.smul_mem _ r hf

/-- Zero extension of the fixed bounded carrier as a real linear map
(BB p. 525). -/
def finiteExtendLinear {a s : ℕ} {p : Fin a → ℕ+} :
    FiniteWordAlgebra a s p →ₗ[ℝ] CoefficientSeries a where
  toFun := extend
  map_add' := extend_add
  map_smul' := extend_smul

/-- A homogeneous series within the cutoff is recovered by zero extension
(BB Proposition 10.42, pp. 523–524). -/
theorem extend_restrict_eq_of_homogeneous {a s k : ℕ} {p : Fin a → ℕ+}
    {f : CoefficientSeries a} (hf : Homogeneous p k f) (hk : k ≤ s) :
    (extend (restrict f : WordCoefficients a s p) : CoefficientSeries a) = f := by
  funext J
  by_cases hJ : wordWeight p J ≤ s
  · exact extend_restrict (fun I => f I) J hJ
  · unfold extend
    rw [dite_eq_right hJ]
    exact (hf J (by omega)).symm

/-- Zero extension of a nested finite commutator is the full commutator
when retained, and zero when above the cutoff (BB pp. 524–525). -/
theorem finiteExtendLinear_nested {a s : ℕ} {p : Fin a → ℕ+}
    (u : Nested (Fin a)) :
    finiteExtendLinear (s := s) (p := p) (u.eval finiteLetter) =
      if wordWeight p u.letters ≤ s then u.eval letterSeries else 0 := by
  by_cases hu : wordWeight p u.letters ≤ s
  · rw [ite_eq_left hu]
    have h := extend_restrict_eq_of_homogeneous
      (f := (formalBracket u.letters : CoefficientSeries a)) (formalBracket_homogeneous p u.letters) hu
    rw [nested_eval_truncatedBracket, nested_eval_formalBracket]
    change (extend (restrict (formalBracket u.letters) : WordCoefficients a s p) :
      CoefficientSeries a) = (formalBracket u.letters : CoefficientSeries a)
    exact h
  · rw [ite_eq_right hu, nested_eval_truncatedBracket]
    have hzero : (truncatedBracket u.letters : FiniteWordAlgebra a s p) = 0 :=
      truncatedBracket_eq_zero_of_weight_gt u.letters (by omega)
    rw [hzero]
    exact (finiteExtendLinear (a := a) (s := s) (p := p)).map_zero

/-- Zero extension of a rational finite Lie polynomial remains a rational
Lie polynomial in the completion (BB Lemma 9.70, p. 472). -/
theorem finiteExtendLinear_mem_rationalLieAlgebra {a s : ℕ} {p : Fin a → ℕ+}
    {f : FiniteWordAlgebra a s p} (hf : f ∈ rationalCoefficientLieAlgebra a s p) :
    finiteExtendLinear f ∈ rationalSeriesLieAlgebra a := by
  rw [rationalCoefficientLieAlgebra_eq_nested] at hf
  rw [rationalSeriesLieAlgebra_eq_nested]
  let P := (finiteExtendLinear (a := a) (s := s) (p := p)).restrictScalars ℚ
  change P f ∈ nestedWordSpan ℚ letterSeries
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨u, rfl⟩ := hg
    change finiteExtendLinear (u.eval finiteLetter) ∈ _
    rw [finiteExtendLinear_nested]
    split
    · exact Submodule.subset_span ⟨u, rfl⟩
    · exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using (nestedWordSpan ℚ letterSeries).zero_mem
  | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul r f _ hf => rw [map_smul]; exact Submodule.smul_mem _ r hf
end RothschildStein.G3

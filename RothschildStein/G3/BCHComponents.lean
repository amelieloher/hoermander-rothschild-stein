-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RationalGrading
public import RothschildStein.G3.GradedLayers
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Universal BCH in an ordinary-degree finite quotient
(BB Theorem 9.68, pp. 469–471). -/
def universalFiniteBCH (s : ℕ) : FiniteWordAlgebra 2 s (fun _ => 1) :=
  ordinaryTrunc s universalBCH

/-- The degree-n universal BCH component in a cutoff-s coefficient algebra
(BB Lemma 9.69, p. 470). -/
def universalComponent (s n : ℕ) : FiniteWordAlgebra 2 s (fun _ => 1) :=
  finiteWeightProjection n (universalFiniteBCH s)

/-- Universal finite BCH is BCH of its two letter generators (BB p. 470). -/
theorem universalFiniteBCH_eq (s : ℕ) : universalFiniteBCH s =
    finiteBCH (finiteLetter (a := 2) (s := s) (p := fun _ => 1) 0) (finiteLetter 1) :=
  ordinaryTrunc_formalBCH (letterSeries_positive 0) (letterSeries_positive 1) s

/-- Finite universal components agree with the completed homogeneous
coefficients (BB pp. 469–470). -/
theorem universalComponent_eq (s n : ℕ) :
    universalComponent s n = ordinaryTrunc s (bchComponent n) := by
  funext J
  change (if wordWeight (fun _ => 1) J.val = n then universalBCH J.val else 0) =
    (if J.val.length = n then universalBCH J.val else 0)
  rw [ordinary_weight]

/-- Each degree-n component has order at least n in every finite quotient
(BB pp. 469–470). -/
theorem universalComponent_order (s n : ℕ) : FiniteOrderAtLeast n (universalComponent s n) := by
  rw [universalComponent_eq]
  change OrderAtLeast (fun _ : Fin 2 => 1) n
    (extend (restrict (fun J => bchComponent n J) : WordCoefficients 2 s (fun _ => 1)))
  apply orderAtLeast_extend_restrict
  intro J hJ
  exact bchComponent_homogeneous n J (by omega)

/-- Universal finite BCH is exactly the sum of its homogeneous components
through the cutoff (BB Theorem 9.68, p. 470). -/
theorem universalFiniteBCH_sum (s : ℕ) :
    (∑ n ∈ Finset.range (s + 1), universalComponent s n) = universalFiniteBCH s :=
  sum_weightProjection (universalFiniteBCH s)

/-- BCH of any positive pair is the exact sum of evaluated universal
components, with no convergence assertion (BB (9.75)–(9.76), pp. 468–470). -/
theorem finiteBCH_components {b s : ℕ} {p : Fin b → ℕ+}
    (X : Fin 2 → FiniteWordAlgebra b s p) (hX : ∀ i, FiniteOrderAtLeast 1 (X i)) :
    finiteBCH (X 0) (X 1) =
      ∑ n ∈ Finset.range (s + 1), finiteSubstitutionHom X hX (universalComponent s n) := by
  have h := congrArg (finiteSubstitutionHom X hX) (universalFiniteBCH_sum s)
  rw [map_sum, universalFiniteBCH_eq, finiteBCH_universal_evaluation] at h
  exact h.symm

/-- Evaluation of a degree-n component has order at least n
(BB Lemma 9.70, p. 472). -/
theorem evaluatedComponent_order {b s : ℕ} {p : Fin b → ℕ+}
    (X : Fin 2 → FiniteWordAlgebra b s p) (hX : ∀ i, FiniteOrderAtLeast 1 (X i)) (n : ℕ) :
    FiniteOrderAtLeast n (finiteSubstitutionHom X hX (universalComponent s n)) :=
  finiteSubstitutionHom_order X hX (universalComponent_order s n)

/-- A known rational Lie component remains a rational Lie polynomial under
positive rational Lie substitution (BB Lemma 9.70, p. 472). -/
theorem evaluatedComponent_mem_rationalLieAlgebra {b s n : ℕ} {p : Fin b → ℕ+}
    (X : Fin 2 → FiniteWordAlgebra b s p) (hX : ∀ i, FiniteOrderAtLeast 1 (X i))
    (hXL : ∀ i, X i ∈ rationalCoefficientLieAlgebra b s p)
    (hn : bchComponent n ∈ rationalSeriesLieAlgebra 2) :
    finiteSubstitutionHom X hX (universalComponent s n) ∈ rationalCoefficientLieAlgebra b s p := by
  apply finiteSubstitution_mem_rationalLieAlgebra X hX hXL
  rw [universalComponent_eq]
  exact truncateSeries_mem_rationalLieAlgebra hn

/-- A universal homogeneous component has its stated degree even after
embedding its finite polynomial representative in the completion (BB p. 470). -/
theorem universalComponent_polynomial_homogeneous (s n : ℕ) :
    Homogeneous (fun _ => 1) n (polynomialSeries 2 (finitePolynomial (universalComponent s n))) := by
  have hp : weightProjection n (universalComponent s n) = universalComponent s n := by
    exact weightProjection_comp n n (universalFiniteBCH s) |>.trans (ite_eq_left rfl)
  have h := homogeneous_extend_of_projection hp
  have he := polynomialSeries_finitePolynomial
    (universalComponent s n : WordCoefficients 2 s (fun _ => 1))
  exact he.symm ▸ h
end RothschildStein.G3

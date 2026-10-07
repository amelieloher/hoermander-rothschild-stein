-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BCHTopOrder
public import Mathlib.LinearAlgebra.Quotient.Defs
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Two prescribed inputs for universal BCH substitution (BB p. 470). -/
def bchPair {L : Type*} (f g : L) : Fin 2 → L := fun i => if i = 0 then f else g

/-- Both entries inherit any common predicate (BB p. 470). -/
theorem bchPair_prop {L : Type*} {P : L → Prop} {f g : L} (hf : P f) (hg : P g) :
    ∀ i, P (bchPair f g i) := by
  intro i
  unfold bchPair
  split
  · exact hf
  · exact hg

/-- The lower-degree part of finite BCH, before the top cutoff component
(BB (9.80), p. 472). -/
def finiteBCHLowerPart {b n : ℕ} {p : Fin b → ℕ+} (f g : FiniteWordAlgebra b n p)
    (hf : FiniteOrderAtLeast 1 f) (hg : FiniteOrderAtLeast 1 g) : FiniteWordAlgebra b n p :=
  ∑ j ∈ Finset.range n, finiteSubstitutionHom (bchPair f g) (bchPair_prop hf hg) (universalComponent n j)

/-- Exact separation of the lower-degree part and the top component
(BB (9.80), p. 472). -/
theorem finiteBCH_eq_lower_add_top {b n : ℕ} {p : Fin b → ℕ+}
    (f g : FiniteWordAlgebra b n p) (hf : FiniteOrderAtLeast 1 f) (hg : FiniteOrderAtLeast 1 g) :
    finiteBCH f g = finiteBCHLowerPart f g hf hg +
      finiteSubstitutionHom (bchPair f g) (bchPair_prop hf hg) (universalComponent n n) := by
  have h := finiteBCH_components (bchPair f g) (bchPair_prop hf hg)
  rw [Finset.sum_range_succ] at h
  simpa only [bchPair, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false, finiteBCHLowerPart] using h

/-- If all lower universal coefficients are rational Lie polynomials,
then the lower BCH part of rational Lie arguments is rational Lie
(BB Lemma 9.70 and (9.80), p. 472). -/
theorem finiteBCHLowerPart_mem_rationalLieAlgebra {b n : ℕ} {p : Fin b → ℕ+}
    (hLow : ∀ j < n, bchComponent j ∈ rationalSeriesLieAlgebra 2)
    (f g : FiniteWordAlgebra b n p) (hf : FiniteOrderAtLeast 1 f) (hg : FiniteOrderAtLeast 1 g)
    (hfL : f ∈ rationalCoefficientLieAlgebra b n p) (hgL : g ∈ rationalCoefficientLieAlgebra b n p) :
    finiteBCHLowerPart f g hf hg ∈ rationalCoefficientLieAlgebra b n p := by
  apply (rationalCoefficientLieAlgebra b n p).toSubmodule.sum_mem
  intro j hj
  exact evaluatedComponent_mem_rationalLieAlgebra _ _ (bchPair_prop hfL hgL)
    (hLow j (Finset.mem_range.mp hj))

/-- The lower BCH part has the same order-one term as the sum of its inputs
(BB (9.80), p. 472). -/
theorem finiteBCHLowerPart_sub_add_order {b n : ℕ} {p : Fin b → ℕ+} (hn : 2 ≤ n)
    (f g : FiniteWordAlgebra b n p) (hf : FiniteOrderAtLeast 1 f) (hg : FiniteOrderAtLeast 1 g) :
    FiniteOrderAtLeast 2 (finiteBCHLowerPart f g hf hg - (f + g)) := by
  have he : finiteBCHLowerPart f g hf hg - (f + g) =
      (finiteBCH f g - (f + g)) -
        finiteSubstitutionHom (bchPair f g) (bchPair_prop hf hg) (universalComponent n n) := by
    rw [finiteBCH_eq_lower_add_top f g hf hg]
    abel
  rw [he]
  exact finiteOrderAtLeast_sub (finiteBCH_sub_add_order hf hg)
    (finiteOrderAtLeast_mono (evaluatedComponent_order _ _ n) hn)

/-- The quotient measuring the obstruction to rational Lie membership
(BB (9.80), p. 472). It is only a vector quotient, since the Lie span need not be
an ideal in the surrounding associative commutator algebra. -/
abbrev rationalLieQuotient (b n : ℕ) (p : Fin b → ℕ+) :=
  FiniteWordAlgebra b n p ⧸ (rationalCoefficientLieAlgebra b n p).toSubmodule

/-- Projection to the rational vector obstruction quotient (BB p. 472). -/
def rationalLieQuotientMap (b n : ℕ) (p : Fin b → ℕ+) :
    FiniteWordAlgebra b n p →ₗ[ℚ] rationalLieQuotient b n p :=
  (rationalCoefficientLieAlgebra b n p).toSubmodule.mkQ

/-- BCH modulo rational Lie polynomials, evaluated on rational Lie
arguments (BB (9.80), p. 472). -/
def rationalBCHClass {b n : ℕ} {p : Fin b → ℕ+}
    (a c : rationalCoefficientLieAlgebra b n p) : rationalLieQuotient b n p :=
  rationalLieQuotientMap b n p (finiteBCH a.val c.val)

/-- Under the induction hypothesis, the obstruction class is exactly the
class of the top evaluated universal component (BB (9.80), p. 472). -/
theorem rationalBCHClass_eq_top {b n : ℕ} {p : Fin b → ℕ+}
    (hLow : ∀ j < n, bchComponent j ∈ rationalSeriesLieAlgebra 2)
    (a c : rationalCoefficientLieAlgebra b n p) :
    rationalBCHClass a c = rationalLieQuotientMap b n p
      (finiteSubstitutionHom (bchPair a.val c.val)
        (bchPair_prop (rationalCoefficientLieAlgebra_positive a.property)
          (rationalCoefficientLieAlgebra_positive c.property)) (universalComponent n n)) := by
  have ha := rationalCoefficientLieAlgebra_positive a.property
  have hc := rationalCoefficientLieAlgebra_positive c.property
  have hmem := finiteBCHLowerPart_mem_rationalLieAlgebra hLow a.val c.val ha hc a.property c.property
  have hz : rationalLieQuotientMap b n p (finiteBCHLowerPart a.val c.val ha hc) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hmem
  change rationalLieQuotientMap b n p (finiteBCH a.val c.val) = _
  rw [finiteBCH_eq_lower_add_top _ _ ha hc, map_add, hz, zero_add]
end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BCHLowerPart
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Scaling both BCH arguments scales the top obstruction by its degree
(BB Lemma 9.70, p. 472). -/
theorem rationalBCHClass_smul {b n : ℕ} {p : Fin b → ℕ+}
    (hLow : ∀ j < n, bchComponent j ∈ rationalSeriesLieAlgebra 2)
    (r : ℚ) (a c : rationalCoefficientLieAlgebra b n p) :
    rationalBCHClass (r • a) (r • c) = r ^ n • rationalBCHClass a c := by
  rw [rationalBCHClass_eq_top hLow, rationalBCHClass_eq_top hLow]
  have he : bchPair (r • a).val (r • c).val = fun i => r • bchPair a.val c.val i := by
    funext i
    simp only [bchPair]
    split <;> rfl
  simp only [he]
  rw [evaluatedComponent_rat_smul, map_smul]

/-- Collinear arguments have zero obstruction, since their commutator
vanishes (BB Lemma 9.70, p. 472). -/
theorem rationalBCHClass_collinear {b n : ℕ} {p : Fin b → ℕ+}
    (a : rationalCoefficientLieAlgebra b n p) (r t : ℚ) :
    rationalBCHClass (r • a) (t • a) = 0 := by
  have ha := rationalCoefficientLieAlgebra_positive (r • a).property
  have hc := rationalCoefficientLieAlgebra_positive (t • a).property
  change FiniteOrderAtLeast 1 (r • a.val) at ha
  change FiniteOrderAtLeast 1 (t • a.val) at hc
  change rationalLieQuotientMap b n p (finiteBCH (r • a.val) (t • a.val)) = 0
  rw [finiteBCH_eq_add_of_commute ha hc ((Commute.refl a.val).smul_left r |>.smul_right t)]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((rationalCoefficientLieAlgebra b n p).add_mem
      ((rationalCoefficientLieAlgebra b n p).smul_mem r a.property)
      ((rationalCoefficientLieAlgebra b n p).smul_mem t a.property))
end RothschildStein.G3

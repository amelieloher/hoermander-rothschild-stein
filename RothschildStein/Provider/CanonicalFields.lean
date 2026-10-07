-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import RothschildStein.Definitions.HomogeneousGroup.horizontalFields
public import RothschildStein.Definitions.HomogeneousGroup.driftFields
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace RothschildStein.Provider

private theorem polynomial_eval_contDiff {N : ℕ}
    (P : MvPolynomial (Fin N ⊕ Fin N) ℝ)
    (g : (Fin N ⊕ Fin N) → ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ)
    (hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => MvPolynomial.eval (fun i => g i x) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ => a))
  | add P Q hP hQ => simpa using hP.add hQ
  | mul_X P i hP => simpa using hP.mul (hg i)

theorem canonicalField_contDiff {N : ℕ} (G : RothschildStein.HomogeneousGroup N)
    (j : Fin N) : ContDiff ℝ (⊤ : ℕ∞) (G.canonicalField j) := by
  have hmul : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G.mul) := by
    apply contDiff_pi.mpr
    intro k
    apply polynomial_eval_contDiff (G.productPolynomial k)
      (fun i z => Sum.elim z.1 z.2 i)
    intro i
    cases i with
    | inl i => exact (contDiff_apply ℝ ℝ i).comp contDiff_fst
    | inr i => exact (contDiff_apply ℝ ℝ i).comp contDiff_snd
  exact hmul.fderiv_apply contDiff_const contDiff_const (by simp)

theorem HomogeneousGroup.horizontalFields_contDiff {N q : ℕ}
    (G : RothschildStein.HomogeneousGroup N) (hq : q ≤ N) (i : Fin q) :
    ContDiff ℝ (⊤ : ℕ∞) (G.horizontalFields hq i) := by
  exact canonicalField_contDiff G (Fin.castLE hq i)

theorem HomogeneousGroup.driftFields_contDiff {N q : ℕ}
    (G : RothschildStein.HomogeneousGroup N) (hq : q + 1 ≤ N) (i : Fin (q + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (G.driftFields hq i) := by
  cases i using Fin.cases with
  | zero => exact canonicalField_contDiff G _
  | succ i => exact canonicalField_contDiff G _

end RothschildStein.Provider

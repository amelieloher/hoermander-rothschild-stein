-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.NestedResidualCorrection
public import RothschildStein.L1.NestedPolynomialPreservation
public import RothschildStein.L1.PolynomialTestAddition
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1
open G3

/-- Complete the finite polynomial induction on
commutator factor count, retaining the exact source total-weight cutoff. -/
theorem exists_polynomial_vanishing_nested_residuals {a s N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (hzero : (0 : Fin N → ℝ) ∈ Ω)
    (hf : FreeAt p s X 0) (c : List (Fin a) → ℝ) (r : ℕ) :
    ∃ (u : MvPolynomial (Fin N) ℝ)
      (hu : ContDiff ℝ (⊤ : ℕ∞) (fun x => MvPolynomial.eval x u)),
      ∀ I : List (Nested (Fin a)), I.length < r → nestedResidualWeight p I ≤ s →
        wordJetResidual Ω X hX (polynomialSmoothTest Ω u hu) 0 c (nestedResidualProduct I) = 0 := by
  induction r with
  | zero =>
    refine ⟨0,?_,?_⟩
    · simpa only [map_zero] using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Fin N → ℝ => (0 : ℝ)))
    · intro I hlen _
      omega
  | succ r ih =>
    obtain ⟨u,hu,hshort⟩ := ih
    obtain ⟨v,hv,hz,hcorrect⟩ := exists_polynomial_nested_residual_correction Ω X hX hzero hf
      (polynomialSmoothTest Ω u hu) c hshort
    have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun x => MvPolynomial.eval x (u+v)) := by
      simpa only [map_add] using hu.add hv
    refine ⟨u+v,hsum,?_⟩
    intro I hlen hw
    rw [polynomialSmoothTest_add Ω u v hu hv hsum,wordJetResidual_test_add]
    by_cases hold : I.length < r
    · rw [hshort I hold hw,differentialPolynomialAt_nested_zero_of_lower_jets Ω X hX hzero v hv hz I hold]
      exact sub_self _
    · have he : I.length = r := by omega
      subst r
      have hc := hcorrect I.get (by simpa only [List.ofFn_get] using hw)
      rw [List.ofFn_get] at hc
      rw [hc]
      exact sub_self _
end RothschildStein.L1

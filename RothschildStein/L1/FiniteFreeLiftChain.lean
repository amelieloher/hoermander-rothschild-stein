-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.PolynomialLiftChains
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- Iterating the actual polynomial one-variable lift terminates
at the formal rank, with a smooth free spanning system and exactly the
required number of added dimensions (BB Theorem 10.19, pp. 493–494). -/
theorem exists_finite_free_polynomial_lift_chain {a s n : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hzero : (0 : Fin n → ℝ) ∈ Ω)
    (hspan : Submodule.span ℝ (range (fun I : BoundedWord a s p =>
      wordBracket X (boundedWordList I) 0)) = ⊤) :
    ∃ N : ℕ, ∃ V : Opens (Fin N → ℝ),
      ∃ Y : Fin a → (Fin N → ℝ) → (Fin N → ℝ),
        N = freeDimension a s p ∧ (0 : Fin N → ℝ) ∈ V ∧
        (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) V) ∧
        FreeAt p s Y 0 ∧
        Submodule.span ℝ (range (fun I : BoundedWord a s p =>
          wordBracket Y (boundedWordList I) 0)) = ⊤ ∧ PolynomialLiftChain X Y := by
  classical
  generalize hd : freeDimension a s p - n = d
  induction d using Nat.strong_induction_on generalizing n with
  | h d ih =>
    by_cases hf : FreeAt p s X 0
    · have hle := freeDimension_le_of_freeAt_unrestricted Ω X hX hzero hf
      have hge := dimension_le_freeDimension_of_word_span_unrestricted Ω X hX hzero hspan
      exact ⟨n,Ω,X,by omega,hzero,hX,hf,hspan,.refl⟩
    · have hlt := dimension_lt_freeDimension_of_nonfree_spanning Ω X hX hzero hspan hf
      obtain ⟨U,hY,hsp⟩ := exists_spanning_polynomial_lift_step Ω X hX hzero hspan hf
      let Y := oneVariableLift X (fun j x => MvPolynomial.eval x (U j))
      have hz : (0 : Fin (n+1) → ℝ) ∈ oneVariableLiftDomain Ω := by
        change P1.paddingBaseCLM n 1 0 ∈ Ω
        simpa only [map_zero] using hzero
      have hde : freeDimension a s p - (n+1) < d := by omega
      obtain ⟨N,V,Z,he,hzZ,hZ,hfZ,hspZ,hchain⟩ :=
        ih (freeDimension a s p - (n+1)) hde (oneVariableLiftDomain Ω) Y hY hz hsp rfl
      exact ⟨N,V,Z,he,hzZ,hZ,hfZ,hspZ,
        (PolynomialLiftChain.step PolynomialLiftChain.refl U).trans hchain⟩
end RothschildStein.L1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.InvariantFormExtension
public import RothschildStein.L1.LeadingWordJets
public import RothschildStein.L1.DirectFreeness
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1
open G3

/-- Freeness turns an actual multilinear
formal residual into one polynomial correcting all its invariant word tuples.
All shorter products are protected by vanishing lower ordinary jets. -/
theorem exists_polynomial_for_invariant_formal_tuples {a s N r : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (hzero : (0 : Fin N → ℝ) ∈ Ω)
    (hf : FreeAt p s X 0) (R : MultilinearMap ℝ (fun _ : Fin r => formalSpan a s p) ℝ) :
    ∃ u : MvPolynomial (Fin N) ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x => MvPolynomial.eval x u) ∧
      (∀ j < r, iteratedFDeriv ℝ j (fun x => MvPolynomial.eval x u) 0 = 0) ∧
      ∀ I : Fin r → List (Fin a), (∀ j, wordWeight p (I j) ≤ s) →
        (∀ e : Equiv.Perm (Fin r), R (fun j => wordLieElement (I (e j))) =
          R (fun j => wordLieElement (I j))) →
        wordDerivative (fun j => wordBracket X (I j)) (List.ofFn (fun j : Fin r => j))
          (fun x => MvPolynomial.eval x u) 0 = R (fun j => wordLieElement (I j)) := by
  have hinj := (freeAt_iff_directPointEvaluation_injective Ω X hX hzero).mp hf
  obtain ⟨H,hsym,hH⟩ := exists_symmetric_form_on_invariant_tuples
    (directPointEvaluation (s := s) (p := p) Ω X hX 0) hinj R
  obtain ⟨u,hu,hz,htop⟩ := exists_polynomial_with_symmetric_top_jet H hsym
  refine ⟨u,hu,hz,?_⟩
  intro I hI hperm
  have hY : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (wordBracket X (I j)) Ω :=
    fun j => G1.wordBracket_contDiffOn Ω.isOpen X hX (I j)
  rw [wordDerivative_eq_top_jet_on Ω _ hY _ hu.contDiffOn hzero (fun j => j) hz,htop]
  have hpoint : (fun j => wordBracket X (I j) 0) =
      (fun j => directPointEvaluation (s := s) (p := p) Ω X hX 0 (wordLieElement (I j))) := by
    funext j
    exact (directPointEvaluation_word Ω X hX (I j) (hI j) hzero).symm
  rw [hpoint]
  exact hH (fun j => wordLieElement (I j)) hperm
end RothschildStein.L1

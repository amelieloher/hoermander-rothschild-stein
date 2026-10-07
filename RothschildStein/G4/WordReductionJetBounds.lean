-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.UniversalReductionBounds
public import RothschildStein.G4.UniformWordJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Actual finite word reductions have a uniform finite coefficient
jet bound depending only on dimensions, family size, maximum word length,
input jet budget, and determinant nondegeneracy. The constant is chosen
before the actual words, fields, or spatial domain. -/
theorem exists_word_reduction_jet_bound (m p n h L : ℕ) (M Δ : ℝ)
    (hM : 0 ≤ M) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω K : Set (Fin n → ℝ)), IsOpen Ω → K ⊆ Ω →
      ∀ (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) →
      (∀ i, HasJetBound Ω K (X i) (h + L) M) →
      ∀ (W : Fin p → List (Fin m)) (I : List (Fin m)),
      (∀ J, (W J).length ≤ L) → I.length ≤ L →
      (∀ x ∈ Ω, determinantSquareSum (fun J => wordBracket X (W J)) x ≠ 0) →
      (∀ x ∈ K, Δ ^ 2 ≤ determinantSquareSum (fun J => wordBracket X (W J)) x) →
      ∀ J, HasJetBound Ω K
        (reductionCoefficient (fun J => wordBracket X (W J)) (wordBracket X I) J) h C := by
  let P := wordJetBase n h L M ^ L
  have hP : 0 ≤ P := pow_nonneg (wordJetBase_nonneg_and_le hM).1 L
  obtain ⟨C, hC, hbound⟩ := exists_universal_reduction_component_jet_bound p n h P P Δ hP hΔ
  refine ⟨C, hC, ?_⟩
  intro Ω K hΩ hKΩ X hX hjets W I hW hI hspan hdet
  have hword : ∀ A : List (Fin m), A.length ≤ L →
      HasJetBound Ω K (wordBracket X A) h P :=
    fun A hA => wordBracket_jet_bound_uniform hΩ hKΩ X hX hM hjets A hA
  apply hbound Ω K hΩ hKΩ _ _
    (fun J => G1.wordBracket_contDiffOn hΩ X hX (W J))
    (G1.wordBracket_contDiffOn hΩ X hX I) hspan _ hdet
    (fun J => hword (W J) (hW J)) (hword I hI)
  intro x hx
  apply (pi_norm_le_iff_of_nonneg hP).mpr
  intro a
  cases a with
  | inl J => simpa using hword (W J) (hW J) 0 (Nat.zero_le h) x hx
  | inr u => simpa using hword I hI 0 (Nat.zero_le h) x hx

end RothschildStein.G4

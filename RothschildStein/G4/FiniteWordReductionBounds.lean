-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WordReductionJetBounds
public import RothschildStein.G4.ReductionReindex

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Universal word reduction jet bounds on any finite word carrier.
The constant is obtained from the numerical cardinality theorem by an
actual reindexing identity, rather than from the chosen coefficient family. -/
theorem exists_finite_word_reduction_jet_bound (ι : Type*) [Fintype ι] [DecidableEq ι]
    (m n h L : ℕ) (M Δ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω K : Set (Fin n → ℝ)), IsOpen Ω → K ⊆ Ω →
      ∀ (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) →
      (∀ i, HasJetBound Ω K (X i) (h + L) M) →
      ∀ (W : ι → List (Fin m)) (I : List (Fin m)),
      (∀ J, (W J).length ≤ L) → I.length ≤ L →
      (∀ x ∈ Ω, determinantSquareSum (fun J => wordBracket X (W J)) x ≠ 0) →
      (∀ x ∈ K, Δ ^ 2 ≤ determinantSquareSum (fun J => wordBracket X (W J)) x) →
      ∀ J, HasJetBound Ω K
        (reductionCoefficient (fun J => wordBracket X (W J)) (wordBracket X I) J) h C := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  obtain ⟨C, hC, hb⟩ := exists_word_reduction_jet_bound m (Fintype.card ι) n h L M Δ hM hΔ
  refine ⟨C, hC, ?_⟩
  intro Ω K hΩ hKΩ X hX hjets W I hW hI hspan hdet J
  have hd := hb Ω K hΩ hKΩ X hX hjets (fun j => W (e j)) I
    (fun j => hW (e j)) hI
    (fun x hx => by rw [determinantSquareSum_reindex e (fun j => wordBracket X (W j))]; exact hspan x hx)
    (fun x hx => by rw [determinantSquareSum_reindex e (fun j => wordBracket X (W j))]; exact hdet x hx) (e.symm J)
  have he : reductionCoefficient (fun j => wordBracket X (W (e j))) (wordBracket X I) (e.symm J) =
      reductionCoefficient (fun j => wordBracket X (W j)) (wordBracket X I) J := by
    simpa only [e.apply_symm_apply] using reductionCoefficient_reindex e
      (fun j => wordBracket X (W j)) (wordBracket X I) (e.symm J)
  rwa [he] at hd

end RothschildStein.G4

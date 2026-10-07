-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.GlobalReduction
public import RothschildStein.G3.FiniteWords
public import RothschildStein.G1.LocalStep

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The nonempty words of weight at most `s`. The full Sobolev word
family also contains the empty word, so geometry filters it. -/
def shortWordFamily {m : ℕ} (w : Fin m → ℕ+) (s : ℕ) : Finset (List (Fin m)) :=
  (wordFamily w s).filter (fun I => I ≠ [])

/-- Finite short-word index carrier. -/
abbrev ShortWord {m : ℕ} (w : Fin m → ℕ+) (s : ℕ) := ↥(shortWordFamily w s)

/-- Membership retains the nonempty and weighted restrictions
(BB conventions, p. 400). -/
theorem mem_shortWordFamily_iff {m s : ℕ} (w : Fin m → ℕ+) (I : List (Fin m)) :
    I ∈ shortWordFamily w s ↔ I ≠ [] ∧ wordWeight w I ≤ s := by
  simp only [shortWordFamily, Finset.mem_filter, G3.mem_wordFamily_iff, and_comm]

/-- Every short word has positive weight, including drift
(BB Definitions 9.3–9.4, p. 402). -/
theorem shortWord_weight_pos {m s : ℕ} {w : Fin m → ℕ+} (I : ShortWord w s) :
    0 < wordWeight w I.val := by
  have hne := ((mem_shortWordFamily_iff w I.val).mp I.property).1
  have hlen : 0 < I.val.length := List.length_pos_iff.mpr hne
  exact hlen.trans_le (G3.length_le_weight w I.val)

/-- Positive weights for the controlled-curve definition. -/
def shortWeight {m s : ℕ} (w : Fin m → ℕ+) (I : ShortWord w s) : ℕ+ :=
  ⟨wordWeight w I.val, shortWord_weight_pos I⟩

/-- Actual short bracket fields, not formal polynomial values. -/
def shortField {m n s : ℕ} (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (I : ShortWord w s) : (Fin n → ℝ) → (Fin n → ℝ) := wordBracket X I.val

/-- All short fields are smooth on the original open domain
(BB Proposition 9.29, p. 421). -/
theorem shortField_contDiffOn {m n s : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (I : ShortWord w s) :
    ContDiffOn ℝ (⊤ : ℕ∞) (shortField w X I) Ω := G1.wordBracket_contDiffOn hΩ X hX I.val

/-- The fixed step hypothesis yields a nondegenerate short frame
at each original-domain point (BB Proposition 9.29, p. 421). -/
theorem exists_short_frame {m n s : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hstep : bracketStepOn Ω w X s) {x : Fin n → ℝ} (hx : x ∈ Ω) :
    ∃ B : Fin n → ShortWord w s, frameDet (shortField w X) B x ≠ 0 := by
  have hspan : Submodule.span ℝ {v | ∃ I ∈ (shortWordFamily w s : Set (List (Fin m))),
      v = wordBracket X I x} = ⊤ := by
    convert hstep x hx using 2
    ext v
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, mem_shortWordFamily_iff]
    aesop
  obtain ⟨I, hI, hdet⟩ := G1.exists_wordFrame_of_span X (shortWordFamily w s) x hspan
  exact ⟨fun j => ⟨I j, hI j⟩, hdet⟩

end RothschildStein.G4

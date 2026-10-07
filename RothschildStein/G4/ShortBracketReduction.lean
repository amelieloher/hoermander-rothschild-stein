-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ReducedCalculus
public import RothschildStein.G1.RankEquivalence

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- A short word embedded in the actual binary bracket carrier. -/
def shortBinaryWord {k s : ℕ} (w : Fin (k + 1) → ℕ+) (I : ShortWord w s) :
    Hormander.Interface.LieWord k :=
  G1.nestedToBinary (G1.exists_nestedWord_of_list I.val
    ((mem_shortWordFamily_iff w I.val).mp I.property).1).choose

/-- The embedding evaluates to the actual short field. -/
theorem shortBinaryWord_eval {k n s : ℕ} (w : Fin (k + 1) → ℕ+)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)) (I : ShortWord w s) :
    Hormander.lieWordEval X (shortBinaryWord w I) = shortField w X I := by
  unfold shortBinaryWord
  rw [G1.nestedToBinary_eval, G1.nestedEval_eq_wordBracket,
    (G1.exists_nestedWord_of_list I.val
      ((mem_shortWordFamily_iff w I.val).mp I.property).1).choose_spec]
  rfl

/-- The embedding retains its weighted length. -/
theorem shortBinaryWord_weight {k s : ℕ} (w : Fin (k + 1) → ℕ+) (I : ShortWord w s) :
    G1.binaryWeight w (shortBinaryWord w I) = (shortWeight w I : ℕ) := by
  unfold shortBinaryWord
  rw [G1.nestedToBinary_weight,
    (G1.exists_nestedWord_of_list I.val
      ((mem_shortWordFamily_iff w I.val).mp I.property).1).choose_spec]
  rfl

/-- Global smooth reduction of a bracket of two short fields. -/
def shortBracketCoefficient {k n s : ℕ} (w : Fin (k + 1) → ℕ+)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (L J K : ShortWord w s) : (Fin n → ℝ) → ℝ :=
  binaryReductionCoefficient w X (.bracket (shortBinaryWord w L) (shortBinaryWord w J)) K

/-- The bracket reduction coefficients are smooth on the original
spanning domain (BB Lemma 9.31 and Proposition 9.36). -/
theorem shortBracketCoefficient_contDiffOn {k n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (L J K : ShortWord w s) :
    ContDiffOn ℝ (⊤ : ℕ∞) (shortBracketCoefficient w X L J K) Ω :=
  binaryReductionCoefficient_contDiffOn hΩ hX hstep _ K

/-- Actual bracket reduction before introducing a frame ratio
(BB Proposition 9.36, pp. 427–428). -/
theorem short_bracket_reduction {k n s : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (L J : ShortWord w s)
    {x : Fin n → ℝ} (hx : x ∈ Ω) :
    VectorField.lieBracket ℝ (shortField w X L) (shortField w X J) x =
      ∑ K, shortBracketCoefficient w X L J K x • shortField w X K x := by
  have h := binary_reduction_representation hΩ hX hstep
    (.bracket (shortBinaryWord w L) (shortBinaryWord w J)) hx
  simpa only [Hormander.lieWordEval, shortBinaryWord_eval, shortBracketCoefficient] using h

/-- Short-bracket reduction has the precise weighted support,
including the drift weight (BB Proposition 9.36, pp. 427–428). -/
theorem shortBracketCoefficient_eq_zero_of_weight_lt {k n s : ℕ}
    (w : Fin (k + 1) → ℕ+) (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (L J K : ShortWord w s)
    (hweight : (shortWeight w L : ℕ) + (shortWeight w J : ℕ) < (shortWeight w K : ℕ)) :
    shortBracketCoefficient w X L J K = 0 := by
  apply binaryReductionCoefficient_eq_zero_of_weight_lt
  change G1.binaryWeight w (shortBinaryWord w L) +
    G1.binaryWeight w (shortBinaryWord w J) < wordWeight w K.val
  rw [shortBinaryWord_weight, shortBinaryWord_weight]
  exact hweight

/-- The fully reduced derivative formula for an actual short-field
Cramer coefficient (BB Proposition 9.36, pp. 427–428). -/
theorem short_fieldDerivative_frameCoefficient {k n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (B : Fin n → ShortWord w s)
    (L J : ShortWord w s) (i : Fin n) {x : Fin n → ℝ}
    (hx : x ∈ Ω) (hB : frameDet (shortField w X) B x ≠ 0) :
    fieldDerivative (shortField w X L) (frameCoefficient (shortField w X) B (shortField w X J) i) x =
      (∑ K, shortBracketCoefficient w X L J K x * frameCoefficient (shortField w X) B (shortField w X K) i x) -
        ∑ j, ∑ K, shortBracketCoefficient w X L (B j) K x *
          (frameCoefficient (shortField w X) B (shortField w X J) j x *
            frameCoefficient (shortField w X) B (shortField w X K) i x) :=
  fieldDerivative_frameCoefficient_of_bracket_reduction hΩ (shortField_contDiffOn hΩ hX)
    _ _ B hx hB (fun J => short_bracket_reduction hΩ hX hstep L J hx) J i

end RothschildStein.G4

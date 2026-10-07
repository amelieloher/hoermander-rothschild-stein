-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.SignedCorrectionList
public import RothschildStein.G3.WeightedLieComponents
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- A finite correction product stays in the finite free Lie carrier
(BB Theorem 9.25, pp. 419–420). -/
theorem correctionProduct_mem_finiteLieSpan {a s : ℕ} {p : Fin a → ℕ+}
    (AS : List (FiniteWordAlgebra a s p))
    (hAS : ∀ A ∈ AS, A ∈ finiteLieSpan a s p) :
    correctionProduct AS ∈ finiteLieSpan a s p := by
  induction AS with
  | nil => exact Submodule.zero_mem _
  | cons A AS ih =>
    exact finiteLieSpan_bch_mem (hAS A (List.mem_cons_self ..))
      (ih (fun B hB => hAS B (List.mem_cons_of_mem A hB)))

/-- Appending correction lists agrees exactly with the finite BCH
product, retaining the chosen pullback order (BB pp. 419–420). -/
theorem correctionProduct_append {a s : ℕ} {p : Fin a → ℕ+}
    (AS BS : List (FiniteWordAlgebra a s p))
    (hAS : ∀ A ∈ AS, A ∈ finiteLieSpan a s p)
    (hBS : ∀ B ∈ BS, B ∈ finiteLieSpan a s p) :
    correctionProduct (AS ++ BS) = finiteBCH (correctionProduct AS) (correctionProduct BS) := by
  have hpos : ∀ CS : List (FiniteWordAlgebra a s p),
      (∀ C ∈ CS, C ∈ finiteLieSpan a s p) → FiniteOrderAtLeast 1 (correctionProduct CS) :=
    fun CS hCS => formalSpan_positive_order _ (correctionProduct_mem_finiteLieSpan CS hCS)
  induction AS with
  | nil =>
    exact (finiteBCH_zero_left (hpos BS hBS)).symm
  | cons A AS ih =>
    have ht : ∀ C ∈ AS, C ∈ finiteLieSpan a s p := fun C hC => hAS C (List.mem_cons_of_mem A hC)
    simp only [List.cons_append, correctionProduct]
    rw [ih ht]
    exact (finiteBCH_assoc
      (formalSpan_positive_order _ (hAS A (List.mem_cons_self ..)))
      (hpos AS ht) (hpos BS hBS)).symm

/-- Raw coefficient product for a signed word correction list. -/
def signedWordProduct {a s : ℕ} {p : Fin a → ℕ+}
    (BS : List (ℝ × List (Fin a))) : FiniteWordAlgebra a s p :=
  correctionProduct (BS.map (fun B => (signedQuasiCorrection B.1 B.2).val))

/-- Signed correction products remain Lie coefficients. -/
theorem signedWordProduct_mem {a s : ℕ} {p : Fin a → ℕ+}
    (BS : List (ℝ × List (Fin a))) :
    signedWordProduct (s := s) (p := p) BS ∈ finiteLieSpan a s p := by
  apply correctionProduct_mem_finiteLieSpan
  intro C hC
  obtain ⟨B, _, rfl⟩ := List.mem_map.mp hC
  exact (signedQuasiCorrection B.1 B.2).property

/-- Finite signed word lists concatenate by the exact BCH law. -/
theorem signedWordProduct_append {a s : ℕ} {p : Fin a → ℕ+}
    (AS BS : List (ℝ × List (Fin a))) :
    signedWordProduct (s := s) (p := p) (AS ++ BS) =
      finiteBCH (signedWordProduct AS) (signedWordProduct BS) := by
  unfold signedWordProduct
  rw [List.map_append]
  apply correctionProduct_append
  all_goals
    intro C hC
    obtain ⟨B, _, rfl⟩ := List.mem_map.mp hC
    exact (signedQuasiCorrection B.1 B.2).property
end RothschildStein.G3

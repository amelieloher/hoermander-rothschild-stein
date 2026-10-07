-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.Grading
public import Mathlib.LinearAlgebra.Basis.VectorSpace
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The bounded nonempty commutator spanning set (BB Definitions 10.43–10.45,
pp. 524–525). -/
def commutatorSet (a s : ℕ) (p : Fin a → ℕ+) : Set (WordCoefficients a s p) :=
  {f | ∃ I, I ≠ [] ∧ wordWeight p I ≤ s ∧ f = truncatedBracket I}

/-- There are finitely many retained commutator vectors (BB p. 525). -/
theorem commutatorSet_finite (a s : ℕ) (p : Fin a → ℕ+) :
    (commutatorSet a s p).Finite := by
  apply (Set.finite_range (fun I : BoundedWord a s p =>
    (truncatedBracket I.val : WordCoefficients a s p))).subset
  intro f hf
  obtain ⟨I, _, hI, rfl⟩ := hf
  exact ⟨boundedWord p I hI, rfl⟩

/-- A finite homogeneous commutator basis can be selected while retaining
all one-letter generators (BB Proposition 10.48 and Remark 10.49, pp. 525–526).
The basis is presented as an independent spanning set of the fixed subspace. -/
theorem exists_homogeneous_commutator_basis {a s : ℕ} (p : Fin a → ℕ+)
    (hp : ∀ i, (p i : ℕ) ≤ s) :
    ∃ B : Set (WordCoefficients a s p), B.Finite ∧
      B ⊆ commutatorSet a s p ∧
      Set.range (fun i : Fin a => (truncatedBracket [i] : WordCoefficients a s p)) ⊆ B ∧
      LinearIndependent ℝ ((↑) : B → WordCoefficients a s p) ∧
      Submodule.span ℝ B = formalSpan a s p ∧
      ∀ f ∈ B, ∃ k, 1 ≤ k ∧ k ≤ s ∧ weightProjection k f = f := by
  let S := Set.range (fun i : Fin a => (truncatedBracket [i] : WordCoefficients a s p))
  have hS : LinearIndepOn ℝ id S := (generators_linearIndependent p hp).linearIndepOn_id
  have hST : S ⊆ commutatorSet a s p := by
    rintro f ⟨i, rfl⟩
    exact ⟨[i], by simp, by simpa [wordWeight] using hp i, rfl⟩
  obtain ⟨B, hBT, hSB, hspan, hB⟩ := exists_linearIndepOn_id_extension hS hST
  refine ⟨B, (commutatorSet_finite a s p).subset hBT, hBT, hSB, hB, ?_, ?_⟩
  · change Submodule.span ℝ B = Submodule.span ℝ (commutatorSet a s p)
    exact le_antisymm (Submodule.span_mono hBT) (Submodule.span_le.mpr hspan)
  · intro f hf
    obtain ⟨I, hne, hI, rfl⟩ := hBT hf
    refine ⟨wordWeight p I, ?_, hI, ?_⟩
    · have hl : 0 < I.length := List.length_pos_iff.mpr hne
      have hw := length_le_weight p I
      omega
    · rw [weightProjection_truncatedBracket]
      exact ite_eq_left rfl

/-- Actual basis of the fixed formal span, with homogeneous commutator
vectors and every generator retained (BB pp. 525–526). -/
theorem exists_homogeneous_basis {a s : ℕ} (p : Fin a → ℕ+)
    (hp : ∀ i, (p i : ℕ) ≤ s) :
    ∃ (B : Set (WordCoefficients a s p)) (b : Module.Basis B ℝ (formalSpan a s p)),
      B.Finite ∧ B ⊆ commutatorSet a s p ∧
      Set.range (fun i : Fin a => (truncatedBracket [i] : WordCoefficients a s p)) ⊆ B ∧
      (∀ f : B, (b f).val = f.val) ∧
      ∀ f : B, ∃ k, 1 ≤ k ∧ k ≤ s ∧ weightProjection k (b f).val = (b f).val := by
  obtain ⟨B, hfin, hBT, hgen, hli, hspan, hhom⟩ := exists_homogeneous_commutator_basis p hp
  have hs : Submodule.span ℝ (Set.range ((↑) : B → WordCoefficients a s p)) = formalSpan a s p := by
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hspan
  let b := (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hs)
  have hb : ∀ f : B, (b f).val = f.val := by
    intro f
    exact Module.Basis.coe_span_apply hli f
  refine ⟨B, b, hfin, hBT, hgen, hb, ?_⟩
  intro f
  simpa only [hb f] using hhom f.val f.property

end RothschildStein.G3

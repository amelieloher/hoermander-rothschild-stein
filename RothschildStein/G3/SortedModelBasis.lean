-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.HomogeneousBasis
public import Mathlib.Data.Fin.Tuple.Sort
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- A homogeneous commutator basis indexed by the fixed free
 dimension, ordered by positive weight and containing every generator
(BB Proposition 10.48 and Remark 10.51, pp. 525–528). -/
theorem exists_sorted_homogeneous_basis {a s : ℕ} (p : Fin a → ℕ+)
    (hp : ∀ i, (p i : ℕ) ≤ s) :
    ∃ (b : Module.Basis (Fin (freeDimension a s p)) ℝ (formalSpan a s p))
      (w : Fin (freeDimension a s p) → ℕ),
      Monotone w ∧ (∀ j, 0 < w j ∧ w j ≤ s) ∧
      (∀ j, weightProjection (w j) (b j).val = (b j).val) ∧
      (∀ j, (b j).val ∈ commutatorSet a s p) ∧
      (∀ i : Fin a, ∃ j, (b j).val = truncatedBracket [i]) := by
  classical
  obtain ⟨B, b, hfin, hBT, hgen, hb, hhom⟩ := exists_homogeneous_basis p hp
  let : Fintype B := hfin.fintype
  have hcard : Fintype.card B = freeDimension a s p := (Module.finrank_eq_card_basis b).symm
  let e₀ := Fintype.equivFinOfCardEq hcard
  let b₀ := b.reindex e₀
  have h₀ : ∀ j : Fin (freeDimension a s p),
      ∃ k, 1 ≤ k ∧ k ≤ s ∧ weightProjection k (b₀ j).val = (b₀ j).val := by
    intro j
    simpa only [b₀, Module.Basis.reindex_apply] using hhom (e₀.symm j)
  let w₀ := fun j => (h₀ j).choose
  have hw₀ := fun j => (h₀ j).choose_spec
  let σ := Tuple.sort w₀
  let b₁ := b₀.reindex σ.symm
  let w := w₀ ∘ σ
  refine ⟨b₁, w, Tuple.monotone_sort w₀, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨(hw₀ (σ j)).1, (hw₀ (σ j)).2.1⟩
  · intro j
    simpa only [b₁, Module.Basis.reindex_apply, Equiv.symm_symm, w, Function.comp_apply] using (hw₀ (σ j)).2.2
  · intro j
    simp only [b₁, b₀, Module.Basis.reindex_apply, Equiv.symm_symm]
    rw [hb]
    exact hBT (e₀.symm (σ j)).property
  · intro i
    let f : B := ⟨truncatedBracket [i], hgen ⟨i, rfl⟩⟩
    refine ⟨σ.symm (e₀ f), ?_⟩
    simp only [b₁, b₀, Module.Basis.reindex_apply, Equiv.symm_symm]
    rw [σ.apply_symm_apply, e₀.symm_apply_apply, hb]
end RothschildStein.G3

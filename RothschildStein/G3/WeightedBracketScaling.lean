-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G1.BracketAlgebra
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.G3

/-- Weighted scaling of primitive fields scales each actual
nested bracket by exactly its word weight, locally on the smooth domain. -/
theorem wordBracket_weighted_scale {a N : ℕ} (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (p : Fin a → ℕ+) (δ : ℝ) (I : List (Fin a))
    {x : Fin N → ℝ} (hx : x ∈ Ω) :
    wordBracket (fun i => δ ^ (p i : ℕ) • X i) I x =
      δ ^ wordWeight p I • wordBracket X I x := by
  induction I generalizing x with
  | nil => simp [wordBracket, smul_zero]
  | cons i I ih =>
    cases I with
    | nil => rfl
    | cons j I =>
      have he : wordBracket (fun k => δ ^ (p k : ℕ) • X k) (j :: I) =ᶠ[𝓝 x]
          δ ^ wordWeight p (j :: I) • wordBracket X (j :: I) := by
        filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
        exact ih hy
      change VectorField.lieBracket ℝ (δ ^ (p i : ℕ) • X i)
        (wordBracket (fun k => δ ^ (p k : ℕ) • X k) (j :: I)) x = _
      rw [EventuallyEq.lieBracket_vectorField_eq (EventuallyEq.rfl) he]
      rw [VectorField.lieBracket_const_smul_left
        (((hX i).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)),
        VectorField.lieBracket_const_smul_right
        (((G1.wordBracket_contDiffOn Ω.isOpen X hX (j :: I)).contDiffAt
          (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp))]
      simp only [wordWeight, List.map_cons, List.sum_cons, pow_add, smul_smul, wordBracket]
end RothschildStein.G3

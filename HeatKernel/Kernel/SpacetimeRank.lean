-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.BlockRank

/-! # The spacetime bracket condition

A nonzero constant time field and a bracket-spanning spatial family generate all
spacetime directions. The same construction applies to two spatial blocks.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

open RothschildStein Hormander.Interface

/-- A nonzero constant field spans the one-dimensional time direction. -/
theorem bracketSpansOn_constant_time {c : ℝ} (hc : c ≠ 0) :
    bracketSpansOn Set.univ (fun (_ : Fin 1) (_ : Fin 1 → ℝ) (_ : Fin 1) => c) := by
  intro z _
  apply top_unique
  intro v _
  have hgen : (fun _ : Fin 1 => c) ∈ Submodule.span ℝ
      {u | ∃ w : List (Fin 1), w ≠ [] ∧
        u = wordBracket (fun (_ : Fin 1) (_ : Fin 1 → ℝ) (_ : Fin 1) => c) w z} :=
    Submodule.subset_span ⟨[0], by simp, rfl⟩
  have heq : v = (v 0 / c) • (fun _ : Fin 1 => c) := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [div_mul_cancel₀ _ hc]
  rw [heq]
  exact Submodule.smul_mem _ _ hgen

/-- A spanning reindexed subfamily suffices for spanning the whole family. -/
theorem bracketSpansOn_of_reindexed {p q n : ℕ} (σ : Fin p → Fin q)
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : bracketSpansOn Set.univ (fun i => X (σ i))) : bracketSpansOn Set.univ X := by
  intro z _
  apply top_unique
  intro v _
  exact inclusion_mem_bracketSpan (fun i => X (σ i)) X (ContinuousLinearMap.id ℝ _) σ z z
    (hX z (Set.mem_univ z)) (fun w => congrFun (wordBracket_map σ X w) z) v

/-- Add a constant time drift as generator zero, followed by the spatial generators. -/
def timeSpaceFields {q n : ℕ} (c : ℝ) (X : Fin q → (Fin n → ℝ) → Fin n → ℝ) :
    Fin (q + 1) → (Fin (1 + n) → ℝ) → Fin (1 + n) → ℝ :=
  fun i => sumFields (fun (_ : Fin 1) (_ : Fin 1 → ℝ) (_ : Fin 1) => c) X
    (i.cast (Nat.add_comm q 1))

@[simp] theorem timeSpaceFields_zero {q n : ℕ} (c : ℝ)
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ) :
    timeSpaceFields c X 0 = fun _ => leftCoordinateInclusion 1 n (fun _ => c) := by
  have hi : Fin.cast (Nat.add_comm q 1) (0 : Fin (q + 1)) =
      Fin.castAdd q (0 : Fin 1) := by ext; rfl
  simp only [timeSpaceFields, hi, sumFields_castAdd]
  rfl

@[simp] theorem timeSpaceFields_succ {q n : ℕ} (c : ℝ)
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ) (i : Fin q) :
    timeSpaceFields c X i.succ = liftRightField 1 (X i) := by
  have hi : Fin.cast (Nat.add_comm q 1) i.succ = Fin.natAdd 1 i := by
    ext
    change i.val + 1 = 1 + i.val
    omega
  simp only [timeSpaceFields, hi, sumFields_natAdd]

/-- A smooth spatial family gives smooth spacetime generators. -/
theorem contDiff_timeSpaceFields {q n : ℕ} (c : ℝ)
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (i : Fin (q + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (timeSpaceFields c X i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [timeSpaceFields_zero]
    exact contDiff_const
  · rw [timeSpaceFields_succ]
    exact (hX j).liftRightField 1

/-- Nonzero time drift upgrades the spatial bracket condition to the spacetime bracket condition. -/
theorem lieAlgebraSpansOn_timeSpaceFields {q n : ℕ} {c : ℝ} (hc : c ≠ 0)
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hspan : bracketSpansOn Set.univ X) :
    LieAlgebraSpansOn Set.univ (timeSpaceFields c X) := by
  apply lieAlgebraSpansOn_of_bracketSpansOn
  apply bracketSpansOn_of_reindexed (fun i : Fin (1 + q) => i.cast (Nat.add_comm 1 q))
  have h := bracketSpansOn_sumFields
    (fun (_ : Fin 1) (_ : Fin 1 → ℝ) (_ : Fin 1) => c) X
    (fun _ => contDiff_const) hX (bracketSpansOn_constant_time hc) hspan
  simpa [timeSpaceFields] using h

/-- A drift and two copies of the spatial generators satisfy the two-block rank condition. -/
theorem lieAlgebraSpansOn_timeTwoSpaceFields {q n : ℕ} {c : ℝ} (hc : c ≠ 0)
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hspan : bracketSpansOn Set.univ X) :
    LieAlgebraSpansOn Set.univ (timeSpaceFields c (sumFields X X)) := by
  apply lieAlgebraSpansOn_timeSpaceFields hc _ _ (bracketSpansOn_sumFields X X hX hX hspan hspan)
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [sumFields_castAdd] using (hX j).liftLeftField n
  · simpa only [sumFields_natAdd] using (hX j).liftRightField n

end HeatKernel

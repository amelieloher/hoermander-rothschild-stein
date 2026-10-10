-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.BlockBrackets
public import HeatKernel.Kernel.WordEmbedding

/-! # Bracket spanning on coordinate products

Spanning in each factor implies spanning for the union of the two lifted families.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

open RothschildStein

/-- Place two families of vector fields in consecutive coordinate blocks. -/
def sumFields {p q m n : ℕ} (X : Fin p → (Fin m → ℝ) → Fin m → ℝ)
    (Y : Fin q → (Fin n → ℝ) → Fin n → ℝ) :
    Fin (p + q) → (Fin (m + n) → ℝ) → Fin (m + n) → ℝ :=
  Fin.addCases (fun i => liftLeftField n (X i)) (fun i => liftRightField m (Y i))

@[simp] theorem sumFields_castAdd {p q m n : ℕ}
    (X : Fin p → (Fin m → ℝ) → Fin m → ℝ)
    (Y : Fin q → (Fin n → ℝ) → Fin n → ℝ) (i : Fin p) :
    sumFields X Y (Fin.castAdd q i) = liftLeftField n (X i) := by
  simp [sumFields]

@[simp] theorem sumFields_natAdd {p q m n : ℕ}
    (X : Fin p → (Fin m → ℝ) → Fin m → ℝ)
    (Y : Fin q → (Fin n → ℝ) → Fin n → ℝ) (i : Fin q) :
    sumFields X Y (Fin.natAdd p i) = liftRightField m (Y i) := by
  simp [sumFields]

/-- Smooth field families remain smooth when placed in separate coordinate blocks. -/
theorem contDiff_sumFields {p q m n : ℕ}
    (X : Fin p → (Fin m → ℝ) → Fin m → ℝ)
    (Y : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hY : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i)) (i : Fin (p + q)) :
    ContDiff ℝ (⊤ : ℕ∞) (sumFields X Y i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [sumFields_castAdd] using (hX j).liftLeftField n
  · simpa only [sumFields_natAdd] using (hY j).liftRightField m

/-- Word transport sends every spatial vector into the target bracket span. -/
theorem inclusion_mem_bracketSpan {p q m n : ℕ}
    (X : Fin p → (Fin m → ℝ) → Fin m → ℝ)
    (Y : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (I : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (σ : Fin p → Fin q)
    (a : Fin m → ℝ) (z : Fin n → ℝ)
    (hspan : Submodule.span ℝ {v | ∃ w : List (Fin p), w ≠ [] ∧ v = wordBracket X w a} = ⊤)
    (hw : ∀ w : List (Fin p), wordBracket Y (w.map σ) z = I (wordBracket X w a))
    (v : Fin m → ℝ) :
    I v ∈ Submodule.span ℝ {v | ∃ w : List (Fin q), w ≠ [] ∧ v = wordBracket Y w z} := by
  let S := Submodule.span ℝ {v | ∃ w : List (Fin q), w ≠ [] ∧ v = wordBracket Y w z}
  have hle : Submodule.span ℝ {v | ∃ w : List (Fin p), w ≠ [] ∧ v = wordBracket X w a} ≤
      S.comap I.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro u ⟨w, hne, rfl⟩
    change I (wordBracket X w a) ∈ S
    rw [← hw]
    apply Submodule.subset_span
    refine ⟨w.map σ, ?_, rfl⟩
    simpa using hne
  rw [hspan] at hle
  exact hle Submodule.mem_top

/-- Bracket-spanning smooth families span the direct sum of their coordinate spaces. -/
theorem bracketSpansOn_sumFields {p q m n : ℕ}
    (X : Fin p → (Fin m → ℝ) → Fin m → ℝ)
    (Y : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hY : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i))
    (hspanX : bracketSpansOn Set.univ X) (hspanY : bracketSpansOn Set.univ Y) :
    bracketSpansOn Set.univ (sumFields X Y) := by
  intro z _
  apply top_unique
  intro v _
  have hleft := inclusion_mem_bracketSpan X (sumFields X Y) (leftCoordinateInclusion m n)
    (Fin.castAdd q) (leftCoordinateProjection m n z) z
    (hspanX _ (Set.mem_univ _)) (fun w => by
      rw [wordBracket_map]
      simp only [sumFields_castAdd]
      rw [wordBracket_liftLeftField n X hX]
      rfl) (leftCoordinateProjection m n v)
  have hright := inclusion_mem_bracketSpan Y (sumFields X Y) (rightCoordinateInclusion m n)
    (Fin.natAdd p) (rightCoordinateProjection m n z) z
    (hspanY _ (Set.mem_univ _)) (fun w => by
      rw [wordBracket_map]
      simp only [sumFields_natAdd]
      rw [wordBracket_liftRightField m Y hY]
      rfl) (rightCoordinateProjection m n v)
  simpa only [coordinateInclusions_add] using Submodule.add_mem _ hleft hright

end HeatKernel

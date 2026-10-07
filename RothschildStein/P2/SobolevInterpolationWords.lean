-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Sobolev
public import RothschildStein.Definitions.sobolevXENorm
public import RothschildStein.Definitions.weakWordENorm

/-!
# Sobolev interpolation, seminorm absorption: the seminorms `Φ_j`

`wordsOfWeight w j` is the family of words of weighted length exactly `j`; in a drift alphabet
(`w 0 = 2`, `w (l+1) = 1`) these are `{[]}` for `j = 0`, `{[l+1]}` for `j = 1` and contain
`[0]` and the `[l+1, l+1]` for `j = 2`. The seminorms
`Φ_j(u) = sup_{1/2 ≤ σ < 1} ((1-σ) r)^j ∑_{|I|=j} ‖X̃_I u‖_{L^p(U_{σ r})}` of the Sobolev interpolation inequality
(BB p. 583) are `seminormPhi`, for a family `U` of open sets (the `ρ`-balls `U_ρ^ρ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein

section Words

variable {k : ℕ} (w : Fin k → ℕ+)

/-- The words of weighted length exactly `j`. -/
def wordsOfWeight (j : ℕ) : Finset (List (Fin k)) :=
  (wordFamily w j).filter (fun I => wordWeight w I = j)

theorem mem_wordsOfWeight {j : ℕ} {I : List (Fin k)} : I ∈ wordsOfWeight w j ↔ wordWeight w I = j := by
  rw [wordsOfWeight, Finset.mem_filter, S.mem_wordFamily_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

/-- The only word of weight zero is the empty word. -/
theorem wordsOfWeight_zero : wordsOfWeight w 0 = {[]} := by
  ext I
  rw [mem_wordsOfWeight, Finset.mem_singleton]
  refine ⟨fun h => ?_, fun h => by subst h; simp [wordWeight]⟩
  have := S.length_le_wordWeight w I
  exact List.length_eq_zero_iff.mp (by omega)

end Words

section Drift

variable {q : ℕ} {w : Fin (q + 1) → ℕ+}

/-- In a drift alphabet the words of weight one are the horizontal letters `[l + 1]`. -/
theorem wordsOfWeight_one (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1) (hw0 : (w 0 : ℕ) = 2) :
    wordsOfWeight w 1 = Finset.univ.image (fun l : Fin q => [l.succ]) := by
  ext I
  rw [mem_wordsOfWeight, Finset.mem_image]
  constructor
  · intro h
    have hlen := S.length_le_wordWeight w I
    rw [h] at hlen
    rcases I with _ | ⟨i, _ | ⟨j, I'⟩⟩
    · simp [wordWeight] at h
    · simp only [wordWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero] at h
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨l, rfl⟩
      · omega
      · exact ⟨l, Finset.mem_univ _, rfl⟩
    · simp at hlen
  · rintro ⟨l, -, rfl⟩
    simp [wordWeight, hw l]

/-- A sum over the words of weight one is the sum over the horizontal letters. -/
theorem sum_wordsOfWeight_one (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1) (hw0 : (w 0 : ℕ) = 2)
    {M : Type*} [AddCommMonoid M] (f : List (Fin (q + 1)) → M) :
    ∑ I ∈ wordsOfWeight w 1, f I = ∑ l : Fin q, f [l.succ] := by
  rw [wordsOfWeight_one hw hw0, Finset.sum_image]
  intro l _ l' _ h
  exact Fin.succ_injective _ (List.singleton_injective h)

/-- The words `[l + 1, l + 1]` and `[0]` have weight two, so a sum over the words of weight two
dominates the sum over them. -/
theorem sum_wordsOfWeight_two_ge (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1) (hw0 : (w 0 : ℕ) = 2)
    (f : List (Fin (q + 1)) → ℝ≥0∞) :
    ∑ l : Fin q, f [l.succ, l.succ] + f [0] ≤ ∑ I ∈ wordsOfWeight w 2, f I := by
  classical
  set T : Finset (List (Fin (q + 1))) :=
    insert [0] (Finset.univ.image (fun l : Fin q => [l.succ, l.succ])) with hT
  have hsub : T ⊆ wordsOfWeight w 2 := by
    intro I hI
    rw [hT, Finset.mem_insert, Finset.mem_image] at hI
    rw [mem_wordsOfWeight]
    rcases hI with rfl | ⟨l, -, rfl⟩
    · simp [wordWeight, hw0]
    · simp [wordWeight, hw l]
  have hnot : [0] ∉ Finset.univ.image (fun l : Fin q => [l.succ, l.succ]) := by simp
  have hinj : Set.InjOn (fun l : Fin q => [l.succ, l.succ]) (Finset.univ : Finset (Fin q)) := by
    intro l _ l' _ h
    have := List.cons.inj h
    exact Fin.succ_injective _ this.1
  calc ∑ l : Fin q, f [l.succ, l.succ] + f [0]
      = f [0] + ∑ l : Fin q, f [l.succ, l.succ] := add_comm _ _
    _ = ∑ I ∈ T, f I := by
        rw [hT, Finset.sum_insert hnot, Finset.sum_image hinj]
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

end Drift

section Phi

variable {k n : ℕ}

/-- The seminorm
`Φ_j(u) = sup_{1/2 ≤ σ < 1} ((1 - σ) r)^j ∑_{|I|=j} ‖X̃_I u‖_{L^p(U_{σ r})}` (BB p. 583), for a family `U` of open sets (the `ρ`-balls `U^ρ_ρ`). -/
def seminormPhi (w : Fin k → ℕ+) (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (U : ℝ → Opens (Fin n → ℝ)) (p : ℝ≥0∞) (r : ℝ) (j : ℕ) (u : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ σ ∈ Set.Ico (1 / 2 : ℝ) 1, ENNReal.ofReal (((1 - σ) * r) ^ j) *
    ∑ I ∈ wordsOfWeight w j, weakWordENorm X (U (σ * r)) I p u

end Phi

end RothschildStein.P2

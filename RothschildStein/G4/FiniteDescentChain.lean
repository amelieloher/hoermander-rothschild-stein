-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.List.Chain
public import Mathlib.Data.Fintype.Card

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Strict descent through finitely many endpoint values gives
an overlap chain without repetition and with a uniform cardinality bound
(BB (9.57), p. 454; explicit termination argument). -/
theorem exists_finite_descending_terminal_chain {ι : Type*} [Fintype ι]
    (level : ι → ℝ) (edge : ι → ι → Prop) (terminal : ι → Prop)
    (hnext : ∀ B, ¬ terminal B → ∃ C, edge B C ∧ level C < level B) (B₀ : ι) :
    ∃ l : List ι, l.IsChain edge ∧ l.Pairwise (fun B C => level C < level B) ∧
      l.head? = some B₀ ∧ (∀ C ∈ l.getLast?, terminal C) ∧
      l.Nodup ∧ l.length ≤ Fintype.card ι := by
  classical
  let rank := fun B => (Finset.univ.filter (fun C => level C < level B)).card
  have hdecrease : ∀ B C, level C < level B → rank C < rank B := by
    intro B C hCB
    have hsub : Finset.univ.filter (fun D => level D < level C) ⊆
        Finset.univ.filter (fun D => level D < level B) := by
      intro D hD
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ((Finset.mem_filter.mp hD).2).trans hCB⟩
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr
      ⟨C, by simp [hCB], by simp⟩)
  have haux : ∀ N : ℕ, ∀ B : ι, rank B = N →
      ∃ l : List ι, l.IsChain edge ∧ l.Pairwise (fun A C => level C < level A) ∧
        l.head? = some B ∧ ∀ C ∈ l.getLast?, terminal C := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro B hBN
      by_cases hBT : terminal B
      · refine ⟨[B], List.isChain_singleton B, by simp, by simp, ?_⟩
        intro C hC
        have hCB : C = B := (show B = C from by simpa using hC).symm
        simpa only [hCB] using hBT
      obtain ⟨C, hBC, hlevel⟩ := hnext B hBT
      have hCN : rank C < N := by rw [← hBN]; exact hdecrease B C hlevel
      obtain ⟨l, hchain, hpair, hhead, hterm⟩ := ih (rank C) hCN C rfl
      cases l with
      | nil => simp at hhead
      | cons A tail =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst A
        refine ⟨B :: C :: tail, ?_, ?_, by simp, ?_⟩
        · apply hchain.cons
          intro D hD
          have hDC : D = C := (show C = D from by simpa using hD).symm
          simpa only [hDC] using hBC
        · apply List.pairwise_cons.mpr
          refine ⟨?_, hpair⟩
          intro D hD
          rcases List.mem_cons.mp hD with hD | hD
          · simpa only [hD] using hlevel
          · exact ((List.pairwise_cons.mp hpair).1 D hD).trans hlevel
        · intro D hD
          exact hterm D (by simpa only [List.getLast?_cons_cons] using hD)
  obtain ⟨l, hchain, hpair, hhead, hterm⟩ := haux (rank B₀) B₀ rfl
  have hnodup : l.Nodup := hpair.imp (fun {B C} hBC hEq => hBC.ne (congrArg level hEq.symm))
  exact ⟨l, hchain, hpair, hhead, hterm, hnodup, hnodup.length_le_card⟩

end RothschildStein.G4

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.HormanderSystem
public import RothschildStein.G1.RankEquivalence
public import RothschildStein.G1.LocalStep
public import RothschildStein.G1.JetBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Hormander.C
namespace RothschildStein.G2
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Abstract and coordinate Lie-word evaluations agree. -/
theorem lieWordEval_eq_frozen
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (t : Hormander.Interface.LieWord q) :
    Hormander.lieWordEval X t = Hormander.Interface.LieWord.eval X t := by
  induction t with
  | generator i => rfl
  | bracket a b ha hb => simp only [Hormander.lieWordEval, Hormander.Interface.LieWord.eval, ha, hb]

private theorem weighted_combination_mem
    (w : Fin (q + 1) → ℕ+) (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) (s : ℕ) (c : WordCombination q)
    (hc : ∀ z ∈ c, wordWeight w (G1.nestedLetters z.2) ≤ s) :
    combinationEval X c x ∈ Submodule.span ℝ
      {v | ∃ I : List (Fin (q + 1)), I ≠ [] ∧ wordWeight w I ≤ s ∧ v = wordBracket X I x} := by
  induction c with
  | nil => exact Submodule.zero_mem _
  | cons z c ih =>
    rcases z with ⟨a, u⟩
    apply Submodule.add_mem _ _ (ih (fun z hz => hc z (by simp [hz])))
    apply Submodule.smul_mem _ (a : ℝ)
    apply Submodule.subset_span
    exact ⟨G1.nestedLetters u, G1.nestedLetters_ne_nil u,
      hc (a, u) (by simp), congrFun (G1.nestedEval_eq_wordBracket X u) x⟩

/-- Weighted binary rank implies the exact
standard-word step premise, with the same step (BB Lemma 1.21, p. 12;
Theorem 3.54, p. 125). -/
theorem bracketStepOn_of_weighted_binary_span
    (w : Fin (q + 1) → ℕ+) (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (s : ℕ)
    (hspan : ∀ x, Submodule.span ℝ (Set.range (fun t :
      {t : Hormander.Interface.LieWord q // G1.binaryWeight w t ≤ s} =>
      Hormander.lieWordEval X t.1 x)) = ⊤) : bracketStepOn univ w X s := by
  intro x _
  apply top_unique
  rw [← hspan x]
  apply Submodule.span_le.mpr
  rintro v ⟨t, rfl⟩
  dsimp only at ⊢
  rw [← binaryExpansion_eqOn isOpen_univ X (fun i => (hX i).contDiffOn) t.1 (mem_univ x)]
  apply weighted_combination_mem w X x s (binaryExpansion t.1)
  intro z hz
  exact (G1.binaryExpansion_weight w t.1 z hz).trans_le t.2

/-- The standard positive integer weights of the homogeneous system. -/
def systemWeights : Fin (q + 1) → ℕ+ := fun i => if i = 0 then 2 else 1

/-- The system grading agrees with the G1 binary grading. -/
theorem system_binaryWeight (t : Hormander.Interface.LieWord q) :
    G1.binaryWeight (systemWeights (q := q)) t =
      lieWordWeight (fun i => if i = 0 then 2 else 1) t := by
  induction t with
  | generator i =>
    simp only [G1.binaryWeight, systemWeights, lieWordWeight]
    split_ifs <;> rfl
  | bracket a b ha hb => simp only [G1.binaryWeight, lieWordWeight, ha, hb]

/-- The original weighted step works at every
point after conversion to standard words (BB pp. 124–125). -/
theorem HomogeneousHormanderSystem.standard_step (H : HomogeneousHormanderSystem G q) :
    bracketStepOn univ systemWeights H.fields H.step := by
  have hs (i) : ContDiff ℝ (⊤ : ℕ∞) (H.fields i) := by
    rw [(H.invariant i).eq_leftField G]
    exact contDiff_leftField G _
  apply bracketStepOn_of_weighted_binary_span systemWeights H.fields hs H.step
  intro x
  let T := {t : Hormander.Interface.LieWord q //
    lieWordWeight (fun i => if i = 0 then 2 else 1) t ≤ H.step}
  have he := invariant_spanning_everywhere G
    (fun t : T => Hormander.Interface.LieWord.eval H.fields t.1)
    (fun t => lieWord_invariant G H.fields H.invariant t.1) H.span_origin x
  apply top_unique
  rw [← he]
  apply Submodule.span_mono
  rintro v ⟨t, rfl⟩
  refine ⟨⟨t.1, ?_⟩, ?_⟩
  · rw [system_binaryWeight]
    exact t.2
  · exact congrFun (lieWordEval_eq_frozen H.fields t.1) x

end RothschildStein.G2

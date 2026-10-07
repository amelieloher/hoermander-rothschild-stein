-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ActualLocalControlUpper
public import RothschildStein.G1.CompactUpperAssembly
public import RothschildStein.G3.FreeModels

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.G1

/-- Smooth bracket-generating weighted fields have the full
compact-uniform control/Euclidean comparison. The field weights are at
most the selected step, as in the no-drift and drift forms of the main theorem.
All actual flows, charts, costs and compact constants are constructed
from these hypotheses (BB Theorem 1.53, pp. 35–36). -/
theorem localControlComparison_of_smooth_bracketStep {a n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (p : Fin a → ℕ+)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hs : 1 ≤ s) (hw : ∀ i, (p i : ℕ) ≤ s) (hstep : bracketStepOn Ω p X s) :
    LocalControlComparison Ω p X s := by
  classical
  rcases Ω.eq_empty_or_nonempty with hΩempty | hΩne
  · intro K _hK hKΩ
    refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
    intro x hx
    exact False.elim (by simpa only [hΩempty, mem_empty_iff_false] using hKΩ hx)
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst n
    intro K _hK hKΩ
    refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
    intro x hx y _hy _hnear
    have he : y = x := Subsingleton.elim _ _
    subst y
    simp only [sub_self, norm_zero, mul_zero, ENNReal.ofReal_zero,
      Real.zero_rpow (by positivity : (1 / (s : ℝ)) ≠ 0),
      controlDistance_self (Ω := Ω) p X (hKΩ hx), le_refl, and_self]
  have ha : 0 < a := by
    by_contra ha
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos ha
    subst a
    obtain ⟨z, hz⟩ := hΩne
    obtain ⟨B, _hB⟩ := G4.exists_short_frame hstep hz
    let I := B ⟨0, hn⟩
    have hI := ((G4.mem_shortWordFamily_iff p I.val).mp I.property).1
    have he : I.val = [] := by
      cases hval : I.val with
      | nil => rfl
      | cons i J => exact Fin.elim0 i
    exact hI he
  exact localControlComparison_of_local_upper hΩ p X (fun i => (hX i).continuousOn)
    (fun z hz => exists_actual_local_control_upper (G3.freeModelData p ha hw) hs hw hn
      hΩ X hX hstep z hz)

end RothschildStein.G1

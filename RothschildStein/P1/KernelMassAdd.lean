-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeKernel
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.P1

variable {N : ℕ}

/-- Absolute row mass is subadditive when the first row is
measurable. The second row may have arbitrary values on a null diagonal. -/
theorem row_mass_add_le
    (f g : (Fin N → ℝ) → ℝ) (hf : AEStronglyMeasurable f volume) :
    (∫⁻ η, ‖f η + g η‖ₑ) ≤ (∫⁻ η, ‖f η‖ₑ) + ∫⁻ η, ‖g η‖ₑ := by
  calc
    _ ≤ ∫⁻ η, ‖f η‖ₑ + ‖g η‖ₑ := lintegral_mono (fun η => enorm_add_le _ _)
    _ = _ := lintegral_add_left' hf.enorm _

/-- Finite sums retain finite uniform row masses. No
joint measurability hypothesis is used in this rowwise statement. -/
theorem exists_list_sum_row_mass_bound {A : Type*} (l : List A)
    (f : A → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hf : ∀ a ∈ l, ∀ ξ, AEStronglyMeasurable (f a ξ) volume)
    (hb : ∀ a ∈ l, ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ ξ, (∫⁻ η, ‖f a ξ η‖ₑ) ≤ B) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ ξ, (∫⁻ η, ‖(l.map (fun a => f a ξ η)).sum‖ₑ) ≤ B := by
  induction l with
  | nil =>
    refine ⟨0, ENNReal.zero_ne_top, ?_⟩
    intro ξ
    simp only [List.map_nil, List.sum_nil, enorm_zero, lintegral_zero, le_refl]
  | cons a l ih =>
    obtain ⟨A, hA, ha⟩ := hb a (by simp)
    obtain ⟨B, hB, hbl⟩ := ih
      (fun b h ξ => hf b (List.mem_cons_of_mem a h) ξ)
      (fun b h => hb b (List.mem_cons_of_mem a h))
    refine ⟨A + B, ENNReal.add_ne_top.mpr ⟨hA, hB⟩, ?_⟩
    intro ξ
    simp only [List.map_cons, List.sum_cons]
    exact (row_mass_add_le (f a ξ) (fun η => (l.map (fun a => f a ξ η)).sum)
      (hf a (by simp) ξ)).trans (add_le_add (ha ξ) (hbl ξ))

end RothschildStein.P1

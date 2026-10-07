-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SelectedAuxiliaryTrajectoryCost

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ENNReal

namespace RothschildStein.G4

/-- With zero auxiliary shift, each selected field contributes
only once, so its strict original-box budget needs no factor two
(BB Theorems 9.11/9.42, pp. 404, 438). -/
theorem selectedAuxiliaryControls_mem_box_zero_shift {m n : ℕ}
    (w : Fin m → ℕ+) (B : Fin n → Fin m) (hB : Function.Injective B)
    {ρ : ℝ} (hρ : 0 < ρ) {u : Fin n → ℝ}
    (hu : u ∈ weightedBox (w ∘ B) ρ) :
    selectedAuxiliaryControls B u 0 ∈ weightedBox w ρ := by
  classical
  intro J
  simp only [selectedAuxiliaryControls, Pi.zero_apply, add_zero]
  by_cases hJ : ∃ i, B i = J
  · obtain ⟨i, rfl⟩ := hJ
    have heq : aggregateMappedControls B u (B i) = u i := by
      simp [aggregateMappedControls, hB.eq_iff]
    rw [heq]
    exact hu i
  · have heq : aggregateMappedControls B u J = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact ite_eq_right (fun hi => hJ ⟨i, hi⟩)
    rw [heq, abs_zero]
    exact pow_pos hρ _

/-- The actual unshifted chart trajectory has constant-field
cost strictly less than its original coefficient radius
(BB Theorems 9.11/9.42, pp. 404, 438). -/
theorem selectedAuxiliaryTrajectory_zero_shift_cost_lt {m n : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (B : Fin n → Fin m) (hB : Function.Injective B)
    {ρ : ℝ} (hρ : 0 < ρ) (u : Fin n → ℝ)
    (hu : u ∈ weightedBox (w ∘ B) ρ)
    (γ : ℝ → (Fin n → ℝ)) (hac : AbsolutelyContinuousOnInterval γ 0 1)
    (hmap : MapsTo γ (Icc (0 : ℝ) 1) Ω)
    (hd : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), HasDerivAt γ
      (∑ j : Fin (n + m), Fin.append u 0 j • Z (Fin.addCases B id j) (γ t)) t) :
    constantControlDistance Ω w Z (γ 0) (γ 1) < ENNReal.ofReal ρ := by
  apply constantControlDistance_endpoint_lt_of_strict_controls Ω w Z γ hac hmap
    (selectedAuxiliaryControls B u 0) hρ
    (selectedAuxiliaryControls_mem_box_zero_shift w B hB hρ hu)
  filter_upwards [hd] with t ht
  rw [selectedAuxiliaryControls_field_eq]
  exact ht

end RothschildStein.G4

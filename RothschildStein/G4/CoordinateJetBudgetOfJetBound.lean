-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.PiJetBounds
public import RothschildStein.G3.CoordinateMultiIndexBudgets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G4

/-- A primitive operator-norm jet budget bounds all coordinate partial words. -/
theorem coordinate_jet_budget_of_jet_bound {m N H : ℕ}
    {Ω K : Set (Fin N → ℝ)} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) {B : ℝ}
    (hj : ∀ i, HasJetBound Ω K (X i) H B) :
    G3.CoordinateMultiIndexBudget K X H B := by
  intro x hx i k hk dirs _ j
  rw [G3.coordinatePartialWord_ofFn_eq_iteratedFDeriv hΩ (hX i) dirs (hKΩ hx)]
  have hm : ‖(fun l : Fin k => (Pi.single (dirs l) (1 : ℝ) : Fin N → ℝ))‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
    intro l
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
    intro a
    by_cases ha : a = dirs l
    · subst a; simp
    · simp [ha]
  have hb : ‖iteratedFDeriv ℝ k (X i) x‖ ≤ B := by
    rw [← iteratedFDerivWithin_of_isOpen k hΩ (hKΩ hx)]
    exact hj i k hk x hx
  calc
    |(iteratedFDeriv ℝ k (X i) x (fun l => Pi.single (dirs l) (1 : ℝ))) j|
        ≤ ‖iteratedFDeriv ℝ k (X i) x (fun l => Pi.single (dirs l) (1 : ℝ))‖ := by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm
            (iteratedFDeriv ℝ k (X i) x (fun l => Pi.single (dirs l) (1 : ℝ))) j
    _ ≤ ‖iteratedFDeriv ℝ k (X i) x‖ :=
      (iteratedFDeriv ℝ k (X i) x).unit_le_opNorm hm
    _ ≤ B := hb
end RothschildStein.G4

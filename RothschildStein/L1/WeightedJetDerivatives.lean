-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.PartialJetCoordinates
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- Ordered coordinate partials compose by concatenating their index lists. -/
theorem rsPartial_append_lists {N : ℕ} (J K : List (Fin N))
    (f : (Fin N → ℝ) → ℝ) : rsPartial (J ++ K) f = rsPartial J (rsPartial K f) := by
  simp only [rsPartial_eq_constant_wordDerivative]
  exact P1.wordDerivative_append _ J K f

/-- Actual coordinate partials preserve smoothness on the original open set. -/
theorem rsPartial_contDiffOn {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (J : List (Fin N)) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (rsPartial J f) Ω := by
  rw [rsPartial_eq_constant_wordDerivative]
  exact S.contDiffOn_wordDerivative Ω _ (fun _ => contDiffOn_const) J f hf

/-- A coordinate derivative lowers its weight
threshold by that coordinate's weight and its ordinary jet order by one. -/
theorem scalarJetVanishing_partial {N p : ℕ} {ω : Fin N → ℕ} {a : ℝ}
    {f : (Fin N → ℝ) → ℝ} (h : scalarJetVanishing ω a (p+1) f)
    (j : Fin N) : scalarJetVanishing ω (a - ω j) p (rsPartial [j] f) := by
  intro J hJ hw
  rw [← rsPartial_append_lists]
  apply h (J ++ [j])
  · simp only [List.length_append, List.length_singleton]; omega
  · simp only [List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, Nat.cast_add]
    linarith

/-- The smooth finite-jet class obeys the same rule. -/
theorem scalarJetClass_partial {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    {ω : Fin N → ℕ} {a : ℝ} {f : (Fin N → ℝ) → ℝ}
    (h : scalarJetClass Ω ω a (p+1) f) (j : Fin N) :
    scalarJetClass Ω ω (a - ω j) p (rsPartial [j] f) :=
  ⟨rsPartial_contDiffOn Ω [j] f h.1, scalarJetVanishing_partial h.2 j⟩
end RothschildStein.L1

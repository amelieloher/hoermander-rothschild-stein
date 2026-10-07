-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ShortReductionJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Hormander.C

namespace RothschildStein.G4

/-- Absolute integer coefficient mass of a finite constant
Jacobi expansion. This is independent of the actual vector fields. -/
def combinationMass {k : ℕ} : WordCombination k → ℝ
  | [] => 0
  | (a, _) :: F => |(a : ℝ)| + combinationMass F

/-- Constant Jacobi coefficient mass is nonnegative. -/
theorem combinationMass_nonneg {k : ℕ} (F : WordCombination k) : 0 ≤ combinationMass F := by
  induction F with
  | nil => exact le_rfl
  | cons z F ih => exact add_nonneg (abs_nonneg _) ih

/-- Reducing an entire constant Jacobi combination propagates
its exact integer coefficient mass into the finite jet budget. -/
theorem combinationReductionCoefficient_jet_bound {k n s : ℕ}
    {Ω K₀ : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hKΩ : K₀ ⊆ Ω)
    (w : Fin (k + 1) → ℕ+) (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (F : WordCombination k) (J : ShortWord w s)
    {h : ℕ} {C : ℝ}
    (hword : ∀ z ∈ F, HasJetBound Ω K₀ (wordReductionCoefficient w X (G1.nestedLetters z.2) J) h C) :
    HasJetBound Ω K₀ (combinationReductionCoefficient w X F J) h (combinationMass F * C) := by
  induction F with
  | nil =>
    simpa only [combinationReductionCoefficient, combinationMass, zero_mul, abs_zero] using
      const_hasJetBound Ω K₀ h 0
  | cons z F ih =>
    obtain ⟨a, u⟩ := z
    have hs := wordReductionCoefficient_contDiffOn hΩ hX hstep (G1.nestedLetters u) J
    have hhead := (hword (a, u) List.mem_cons_self).const_mul hΩ hKΩ hs (a : ℝ)
    have htail := ih (fun z hz => hword z (List.mem_cons_of_mem _ hz))
    have hb := hhead.add hΩ hKΩ (contDiffOn_const.mul hs)
      (combinationReductionCoefficient_contDiffOn hΩ hX hstep F J) htail
    convert hb using 1
    · rfl
    · change (|(a : ℝ)| + combinationMass F) * C = _
      ring

end RothschildStein.G4

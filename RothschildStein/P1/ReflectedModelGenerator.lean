-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.InputBracketApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The reflected model generator is smooth globally. -/
theorem reflectedGenerator_contDiff (i : Fin k) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u => C.Y i (-u)) :=
  (C.model_field_smooth i).comp contDiff_id.neg

/-- Reflection preserves the generator's weighted degree. -/
theorem reflectedGenerator_homogeneous (i : Fin k) :
    G2.IsHomogeneousField C.G (fun u => C.Y i (-u)) ((w i : ℕ) : ℝ) := by
  intro t ht u
  simpa only [G2.dilate_neg] using C.isHomogeneousField i t ht (-u)

end RothschildStein.P1.LiftedChart

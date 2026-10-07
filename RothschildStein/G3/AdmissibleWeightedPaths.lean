-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.TimedSchedulePathBounds
public import RothschildStein.G3.ActualQuasiExponentialPoints
public import RothschildStein.G3.SignedPrimitiveCoordinates
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.G3

/-- Admissible weighted schedules stay in the flow range along every whole arc. -/
theorem timedScheduleInside_of_weighted_admissible {a N : ℕ} (p : Fin a → ℕ+)
    (Ψ : Fin a → ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (U Ω : Set (Fin N → ℝ)) {κ t : ℝ}
    (hrange : ∀ i y, y ∈ U → ∀ v ∈ Ioo (-κ) κ, Ψ i (y,v) ∈ Ω)
    (S : List (Fin a × Bool)) (x : Fin N → ℝ)
    (h : G1.FlowScheduleAdmissible Ψ (fun i t => t^(p i : ℕ))
      (fun _ => U) (fun _ => κ) t S x) :
    TimedScheduleInside Ψ Ω (S.map (fun b => (b.1,signedPrimitiveTime p b t))) x := by
  induction S generalizing x with
  | nil => trivial
  | cons b S ih =>
    refine ⟨?_,?_⟩
    · intro θ hθ
      apply hrange b.1 x h.1
      apply abs_lt.mp
      rw [abs_mul,abs_of_nonneg hθ.1]
      have ht : |signedPrimitiveTime p b t| < κ := by
        rw [signedPrimitiveTime_abs,← abs_pow]
        exact abs_lt.mpr h.2.1
      exact (mul_le_mul_of_nonneg_right hθ.2 (abs_nonneg (signedPrimitiveTime p b t))).trans_lt
        (by simpa only [one_mul] using ht)
    · exact ih _ h.2.2.2
end RothschildStein.G3

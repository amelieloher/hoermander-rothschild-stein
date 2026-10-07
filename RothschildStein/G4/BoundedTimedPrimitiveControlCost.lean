-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.TimedPrimitiveControlCost

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.G4
open G3 G1

/-- The bound A δ^weight on actual primitive times
implies an ordinary cost linear in δ, including unequal letter weights
(BB p. 460, (9.70)). -/
theorem controlDistance_bounded_timed_primitive_schedule {m n : ℕ}
    {Ω U : Set (Fin n → ℝ)} (hUΩ : U ⊆ Ω)
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    {τ δ A : ℝ} (hδ : 0 < δ)
    (Φ : Fin m → ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hΦ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Φ i) (U ×ˢ Ioo (-τ) τ))
    (hODE : ∀ i x, x ∈ U → Φ i (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun t => Φ i (x, t)) (X i (Φ i (x, v))) v ∧ Φ i (x, v) ∈ Ω)
    (S : List (Fin m × ℝ))
    (htime : ∀ b ∈ S, |b.2| < τ)
    (hcost : ∀ b ∈ S, |b.2| ≤ A * δ ^ (w b.1 : ℕ))
    {x : Fin n → ℝ} (hx : x ∈ U) (hinside : TimedScheduleInside Φ U S x) :
    controlDistance Ω w X x (runTimedPrimitiveSchedule Φ S x) ≤
      ENNReal.ofReal ((S.length : ℝ) * max 1 A * δ) := by
  have hA : 0 < max 1 A := zero_lt_one.trans_le (le_max_left _ _)
  have hb : ∀ b ∈ S, |b.2| ≤ (max 1 A * δ) ^ (w b.1 : ℕ) := by
    intro b hb
    calc
      _ ≤ A * δ ^ (w b.1 : ℕ) := hcost b hb
      _ ≤ (max 1 A) ^ (w b.1 : ℕ) * δ ^ (w b.1 : ℕ) :=
        mul_le_mul_of_nonneg_right
          ((le_max_right 1 A).trans (le_self_pow₀ (le_max_left 1 A) (w b.1).pos.ne'))
          (pow_nonneg hδ.le _)
      _ = _ := (mul_pow _ _ _).symm
  have hh := controlDistance_timed_primitive_schedule hUΩ w X (mul_pos hA hδ)
    Φ hΦ hODE S htime hb hx hinside
  simpa only [mul_assoc] using hh

end RothschildStein.G4

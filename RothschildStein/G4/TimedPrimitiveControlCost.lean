-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalFlowArcCost
public import RothschildStein.G3.TimedSchedulePathBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.G4
open G3 G1

/-- The actual buffered timed schedule returned by the buffered primitive construction has
ordinary control cost at most its length times its weighted arc budget.
This retains each genuine intermediate endpoint (BB pp. 459–460). -/
theorem controlDistance_timed_primitive_schedule {m n : ℕ}
    {Ω U : Set (Fin n → ℝ)} (hUΩ : U ⊆ Ω)
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    {τ δ : ℝ} (hδ : 0 < δ)
    (Φ : Fin m → ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hΦ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Φ i) (U ×ˢ Ioo (-τ) τ))
    (hODE : ∀ i x, x ∈ U → Φ i (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun t => Φ i (x, t)) (X i (Φ i (x, v))) v ∧ Φ i (x, v) ∈ Ω)
    (S : List (Fin m × ℝ))
    (htime : ∀ b ∈ S, |b.2| < τ)
    (hcost : ∀ b ∈ S, |b.2| ≤ δ ^ (w b.1 : ℕ))
    {x : Fin n → ℝ} (hx : x ∈ U) (hinside : TimedScheduleInside Φ U S x) :
    controlDistance Ω w X x (runTimedPrimitiveSchedule Φ S x) ≤
      ENNReal.ofReal ((S.length : ℝ) * δ) := by
  induction S generalizing x with
  | nil =>
    simp only [runTimedPrimitiveSchedule, controlDistance_self (Ω := Ω) w X (hUΩ hx),
      List.length_nil, Nat.cast_zero, zero_mul, ENNReal.ofReal_zero, le_refl]
  | cons b S ih =>
    have hend : Φ b.1 (x, b.2) ∈ U := by
      simpa only [one_mul] using hinside.1 1 (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    have hfirst := controlDistance_local_flow_arc w X b.1 hδ (Φ b.1) (hΦ b.1) hx
      (hODE b.1 x hx).1 (hODE b.1 x hx).2
      (htime b (List.mem_cons_self ..)) (hcost b (List.mem_cons_self ..))
    have hnext := ih (fun c hc => htime c (List.mem_cons_of_mem b hc))
      (fun c hc => hcost c (List.mem_cons_of_mem b hc)) hend hinside.2
    calc
      _ ≤ controlDistance Ω w X x (Φ b.1 (x, b.2)) +
          controlDistance Ω w X (Φ b.1 (x, b.2))
            (runTimedPrimitiveSchedule Φ S (Φ b.1 (x, b.2))) :=
        controlDistance_triangle Ω w X _ _ _
      _ ≤ ENNReal.ofReal δ + ENNReal.ofReal ((S.length : ℝ) * δ) := add_le_add hfirst hnext
      _ = _ := by
        rw [← ENNReal.ofReal_add hδ.le (by positivity)]
        congr 1
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

end RothschildStein.G4

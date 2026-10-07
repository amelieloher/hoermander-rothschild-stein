-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalFlowArcCost
public import RothschildStein.G3.ActualQuasiExponentialPoints

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.G1

/-- The actual weighted primitive schedule costs at most its
length times the scalar dilation. All starting domains and intermediate
endpoints are those of the genuine local flows (BB pp. 34–35). -/
theorem controlDistance_weighted_schedule {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (U : Fin m → Set (Fin n → ℝ)) (hUΩ : ∀ i, U i ⊆ Ω)
    (τ : Fin m → ℝ)
    (Φ : Fin m → ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hΦ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Φ i) (U i ×ˢ Ioo (-τ i) (τ i)))
    (hODE : ∀ i x, x ∈ U i → Φ i (x, 0) = x ∧ ∀ v ∈ Ioo (-τ i) (τ i),
      HasDerivAt (fun z => Φ i (x, z)) (X i (Φ i (x, v))) v ∧ Φ i (x, v) ∈ Ω)
    (t : ℝ) (ht : t ≠ 0) (S : List (Fin m × Bool))
    (x : Fin n → ℝ) (hx : x ∈ Ω)
    (hS : FlowScheduleAdmissible Φ (fun i t => t ^ (w i : ℕ)) U τ t S x) :
    controlDistance Ω w X x (runSchedule
      (fun b y => G3.weightedPrimitiveArc w Φ b (t, y)) S x) ≤
      ENNReal.ofReal ((S.length : ℝ) * |t|) := by
  induction S generalizing x with
  | nil => simp only [runSchedule, controlDistance_self w X hx, List.length_nil,
      Nat.cast_zero, zero_mul, ENNReal.ofReal_zero, le_refl]
  | cons b S ih =>
    obtain ⟨hxU, htime, hend, hrest⟩ := hS
    let T : ℝ := if b.2 then t ^ (w b.1 : ℕ) else -(t ^ (w b.1 : ℕ))
    have hTabs : |T| = |t| ^ (w b.1 : ℕ) := by
      dsimp [T]
      split <;> simp only [abs_neg, abs_pow]
    have hTτ : |T| < τ b.1 := by
      rw [hTabs, ← abs_pow]
      exact abs_lt.mpr htime
    have hfirst : controlDistance Ω w X x (Φ b.1 (x, T)) ≤ ENNReal.ofReal |t| :=
      controlDistance_local_flow_arc w X b.1 (abs_pos.mpr ht) (Φ b.1)
        (hΦ b.1) hxU (hODE b.1 x hxU).1 (hODE b.1 x hxU).2 hTτ hTabs.le
    have hnext := ih (Φ b.1 (x, T)) (hUΩ b.1 hend) hrest
    have htri := controlDistance_triangle Ω w X x (Φ b.1 (x, T))
      (runSchedule (fun b y => G3.weightedPrimitiveArc w Φ b (t, y)) S (Φ b.1 (x, T)))
    calc
      _ ≤ _ := htri
      _ ≤ ENNReal.ofReal |t| + ENNReal.ofReal ((S.length : ℝ) * |t|) :=
        add_le_add hfirst hnext
      _ = _ := by
        rw [← ENNReal.ofReal_add (abs_nonneg _) (by positivity)]
        congr 1
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

end RothschildStein.G1

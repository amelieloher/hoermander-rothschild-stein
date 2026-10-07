-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlledReparam
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal

namespace RothschildStein.G1

/-- A nondegenerate subcurve with weights one or two has parameter
sqrt(b-a)*δ; the square-root factor is essential for drift
(BB Rem 1.39, p. 22). -/
theorem isControlledCurve_subcurve {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hw : ∀ i, (w i : ℕ) ≤ 2) {δ : ℝ} {γ : ℝ → (Fin n → ℝ)}
    (hγ : isControlledCurve Ω w X δ γ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    isControlledCurve Ω w X (Real.sqrt (b - a) * δ) (fun t => γ (a + (b - a) * t)) := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hd1 : b - a ≤ 1 := by linarith
  apply isControlledCurve_comp_affine hγ (mul_pos (Real.sqrt_pos.mpr hd) hγ.1) (ne_of_gt hd)
  · intro t ht
    constructor <;> dsimp
    · nlinarith [ht.1, ht.2]
    · nlinarith [ht.1, ht.2]
  · intro i
    rw [abs_of_pos hd]
    have hi := (w i).pos
    rcases (show (w i : ℕ) = 1 ∨ (w i : ℕ) = 2 by have := hw i; omega) with h | h
    · simp only [h, pow_one]
      exact mul_le_mul_of_nonneg_right ((Real.le_sqrt hd.le hd.le).mpr (by nlinarith)) hγ.1.le
    · rw [h, mul_pow, Real.sq_sqrt hd.le]

/-- Weighted subcurve distance bound, including the degenerate interval
(BB Rem 1.39, p. 22). -/
theorem controlDistance_subcurve_le {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hw : ∀ i, (w i : ℕ) ≤ 2) {δ : ℝ} {γ : ℝ → (Fin n → ℝ)}
    (hγ : isControlledCurve Ω w X δ γ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    controlDistance Ω w X (γ a) (γ b) ≤ ENNReal.ofReal (Real.sqrt (b - a) * δ) := by
  rcases eq_or_lt_of_le hab with h | h
  · subst b
    rw [controlDistance_self w X (hγ.2.2.1 ⟨ha, hb⟩)]
    exact bot_le
  · have hm := controlDistance_le_of_curve (isControlledCurve_subcurve hw hγ ha h hb)
    simpa only [mul_zero, add_zero, mul_one, add_sub_cancel] using hm

/-- The initial segment of a weighted controlled curve costs at most
sqrt(t)*δ (BB Rem 1.39, p. 22). -/
theorem controlDistance_initial_subcurve_le {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hw : ∀ i, (w i : ℕ) ≤ 2) {δ : ℝ} {γ : ℝ → (Fin n → ℝ)}
    (hγ : isControlledCurve Ω w X δ γ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    controlDistance Ω w X (γ 0) (γ t) ≤ ENNReal.ofReal (Real.sqrt t * δ) := by
  simpa only [sub_zero] using controlDistance_subcurve_le hw hγ le_rfl ht.1 ht.2

end RothschildStein.G1

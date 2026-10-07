-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.NumericalForwardBuffer

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators

namespace RothschildStein.G4

/-- The actual flow stays in the open primitive-jet buffer on the
whole prescribed time interval, with clearance chosen numerically. -/
theorem numerical_timeOne_open_buffer {m n : ℕ} {K : Set (Fin n → ℝ)}
    (W : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (x₀ : Fin n → ℝ) {R δ A : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hA : 0 ≤ A)
    (hδR : δ ≤ R / (64 * (1 + A)))
    (Φ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hΦ : ∀ a ∈ ball 0 δ, ∀ x ∈ ball x₀ (R / 4), Φ ((a, x), 0) = x ∧
      ∀ t ∈ Ioo (-2 : ℝ) 2, Φ ((a, x), t) ∈ K ∧
        HasDerivAt (fun v => Φ ((a, x), v))
          (∑ j, a j • W j (Φ ((a, x), t))) t)
    (hbound : ∀ y ∈ K, ∑ j, ‖W j y‖ ≤ A)
    {a : Fin m → ℝ} (ha : a ∈ ball 0 δ)
    {x : Fin n → ℝ} (hx : x ∈ ball x₀ (R / 4))
    {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    Φ ((a, x), t) ∈ ball x₀ R := by
  have han : ‖a‖ ≤ δ :=
    (by simpa only [mem_ball, dist_zero_right] using ha : ‖a‖ < δ).le
  have hprod : δ * (64 * (1 + A)) ≤ R :=
    (le_div_iff₀ (by positivity)).mp hδR
  have hδA : δ * A ≤ R / 64 := by nlinarith
  have hd := timeOneFlow_displacement_le W a (fun v => Φ ((a, x), v))
    (hΦ a ha x hx).1 (hΦ a ha x hx).2 hA hbound ht
  have habst : |t| ≤ 2 := (abs_lt.mpr ht).le
  have hspeed : ‖a‖ * A ≤ δ * A := mul_le_mul_of_nonneg_right han hA
  have hdR : ‖Φ ((a, x), t) - x‖ ≤ R / 32 := by
    calc
      _ ≤ (‖a‖ * A) * |t| := hd
      _ ≤ (δ * A) * 2 := mul_le_mul hspeed habst (abs_nonneg _) (mul_nonneg hδ.le hA)
      _ ≤ R / 32 := by linarith
  rw [mem_ball, dist_eq_norm] at hx ⊢
  have htri : ‖Φ ((a, x), t) - x₀‖ ≤ ‖Φ ((a, x), t) - x‖ + ‖x - x₀‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (Φ ((a, x), t) - x) (x - x₀)
  linarith

end RothschildStein.G4

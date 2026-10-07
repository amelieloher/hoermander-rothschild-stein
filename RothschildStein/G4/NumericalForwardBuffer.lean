-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.MappedShortTimeOneFlow
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators

namespace RothschildStein.G4

/-- The actual constant-coefficient flow displacement is bounded
by coefficient norm times the total field-value budget and elapsed time.
Only field values on the actual trajectory buffer are used. -/
theorem timeOneFlow_displacement_le {m n : ℕ} {K : Set (Fin n → ℝ)}
    (W : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (a : Fin m → ℝ)
    (γ : ℝ → (Fin n → ℝ)) {x : Fin n → ℝ} (hinit : γ 0 = x)
    (hγ : ∀ t ∈ Ioo (-2 : ℝ) 2, γ t ∈ K ∧
      HasDerivAt γ (∑ j, a j • W j (γ t)) t)
    {A : ℝ} (_hA : 0 ≤ A) (hbound : ∀ y ∈ K, ∑ j, ‖W j y‖ ≤ A)
    {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    ‖γ t - x‖ ≤ (‖a‖ * A) * |t| := by
  have hZ : ∀ y ∈ K, ‖∑ j, a j • W j y‖ ≤ ‖a‖ * A := by
    intro y hy
    calc
      _ ≤ ∑ j, ‖a j • W j y‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖a‖ * ‖W j y‖ := Finset.sum_le_sum (fun j _ => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm a j) (norm_nonneg _))
      _ = ‖a‖ * ∑ j, ‖W j y‖ := by rw [Finset.mul_sum]
      _ ≤ ‖a‖ * A := mul_le_mul_of_nonneg_left (hbound y hy) (norm_nonneg _)
  have hsub : uIcc 0 t ⊆ Ioo (-2 : ℝ) 2 :=
    ordConnected_Ioo.uIcc_subset (by constructor <;> norm_num) ht
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v hv => ((hγ v (hsub hv)).2).hasDerivWithinAt)
    (fun v hv => hZ _ (hγ v (hsub hv)).1)
    (convex_uIcc (0 : ℝ) t) left_mem_uIcc right_mem_uIcc
  simpa only [hinit, sub_zero, Real.norm_eq_abs] using hh

/-- The prescribed numerical coefficient radius forces every
forward segment into the original initial-point flow patch. It supplies
uniform clearance for the actual differentiated remainder (BB pp. 441–444). -/
theorem numerical_timeOne_forward_buffer {m n : ℕ} {K : Set (Fin n → ℝ)}
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
    {x : Fin n → ℝ} (hx : x ∈ ball x₀ (R / 8)) :
    ∀ t ∈ Icc (0 : ℝ) 1, Φ ((a, x), t) ∈ ball x₀ (R / 4) := by
  have hxin : x ∈ ball x₀ (R / 4) := ball_subset_ball (by linarith) hx
  have han : ‖a‖ ≤ δ := (by simpa only [mem_ball, dist_zero_right] using ha : ‖a‖ < δ).le
  have hprod : δ * (64 * (1 + A)) ≤ R := (le_div_iff₀ (by positivity)).mp hδR
  have hδA : δ * A ≤ R / 64 := by nlinarith
  intro t ht
  have htime : t ∈ Ioo (-2 : ℝ) 2 := by constructor <;> linarith [ht.1, ht.2]
  have hd := timeOneFlow_displacement_le W a (fun v => Φ ((a, x), v))
    (hΦ a ha x hxin).1 (hΦ a ha x hxin).2 hA hbound htime
  have habst : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hspeed : ‖a‖ * A ≤ δ * A := mul_le_mul_of_nonneg_right han hA
  have hdR : ‖Φ ((a, x), t) - x‖ ≤ R / 64 :=
    hd.trans ((mul_le_of_le_one_right (mul_nonneg (norm_nonneg a) hA) habst).trans
      (hspeed.trans hδA))
  rw [mem_ball, dist_eq_norm] at hx ⊢
  have htri : ‖Φ ((a, x), t) - x₀‖ ≤ ‖Φ ((a, x), t) - x‖ + ‖x - x₀‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (Φ ((a, x), t) - x) (x - x₀)
  linarith

end RothschildStein.G4

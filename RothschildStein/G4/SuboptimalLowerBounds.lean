-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.Suboptimality

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Positive frame weights are nonnegative. -/
theorem frameWeight_nonneg {ι : Type*} {n : ℕ} (w : ι → ℕ+) (B : Fin n → ι) :
    0 ≤ frameWeight w B := Finset.sum_nonneg (fun _ _ => by positivity)

/-- A uniform short-word cutoff bounds every frame weight. -/
theorem frameWeight_le {ι : Type*} {n : ℕ} (w : ι → ℕ+) (s : ℕ)
    (hw : ∀ i, (w i : ℕ) ≤ s) (B : Fin n → ι) : frameWeight w B ≤ (n * s : ℕ) := by
  have he : frameWeight w B ≤ ∑ _ : Fin n, (s : ℤ) :=
    Finset.sum_le_sum (fun i _ => by exact_mod_cast hw (B i))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_mul] using he

/-- Suboptimality and the uniform determinant maximum lower bound
supply the absolute Taylor-remainder denominator, with no additional
inverse-suboptimality factors. -/
theorem suboptimal_frameDet_lower_bound {ι : Type*} {n : ℕ}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} (w : ι → ℕ+) (s : ℕ)
    (hw : ∀ i, (w i : ℕ) ≤ s) (B : Fin n → ι) {x : Fin n → ℝ}
    {t r Δ : ℝ} (ht : 0 < t) (hr : 0 < r) (hr1 : r ≤ 1) (_hΔ : 0 ≤ Δ)
    (hmax : ∃ C : Fin n → ι, Δ ≤ |frameDet Z C x|)
    (hB : IsSuboptimal Z w B x t r) :
    t * Δ * r ^ (n * s) ≤ |frameDet Z B x| := by
  obtain ⟨C, hC⟩ := hmax
  have hwC := frameWeight_le w s hw C
  have hp : r ^ (n * s) ≤ r ^ frameWeight w C := by
    rw [← zpow_natCast]
    exact zpow_le_zpow_right_of_le_one₀ hr hr1 hwC
  have hBpow : r ^ frameWeight w B ≤ 1 :=
    zpow_le_one₀ hr hr1 (frameWeight_nonneg w B)
  calc
    _ ≤ t * |frameDet Z C x| * r ^ frameWeight w C :=
      mul_le_mul (mul_le_mul_of_nonneg_left hC ht.le) hp (pow_nonneg hr.le _) (by positivity)
    _ ≤ |frameDet Z B x| * r ^ frameWeight w B := by simpa only [mul_assoc] using hB C
    _ ≤ |frameDet Z B x| := by nlinarith [abs_nonneg (frameDet Z B x)]

end RothschildStein.G4

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.VolumePolynomial

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- A maximizing frame's original weighted box dominates a
fixed fraction of the full volume polynomial (BB proof of Theorem 9.12,
p. 405; original-radius lower bound). -/
theorem chart_box_scalar_lower_bound {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (w : ι → ℕ) (D : ℕ) (hw : ∀ i, w i ≤ D) (B : ι)
    {a r K : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hr : 0 ≤ r) (hK : 0 ≤ K)
    (hmax : ∀ C, |lam C| * r ^ w C ≤ |lam B| * r ^ w B) :
    (K * a ^ D / (Fintype.card ι : ℝ)) * volumePolynomial lam w r ≤
      K * |lam B| * (a * r) ^ w B := by
  have hc : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨B⟩
  have hp := volumePolynomial_le_card_mul_of_maximizer lam w r B hmax
  have hpow : a ^ D ≤ a ^ w B := pow_le_pow_of_le_one ha.le ha1 (hw B)
  calc
    _ ≤ (K * a ^ D / (Fintype.card ι : ℝ)) *
        ((Fintype.card ι : ℝ) * (|lam B| * r ^ w B)) :=
      mul_le_mul_of_nonneg_left hp (div_nonneg (mul_nonneg hK (pow_nonneg ha.le D)) hc.le)
    _ = K * a ^ D * (|lam B| * r ^ w B) := by field_simp
    _ ≤ K * a ^ w B * (|lam B| * r ^ w B) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK)
        (mul_nonneg (abs_nonneg _) (pow_nonneg hr _))
    _ = K * |lam B| * (a * r) ^ w B := by rw [mul_pow]; ring

/-- Applying the chart at the larger radius r/b controls its
actual image-volume scalar by the original-radius polynomial; no
Jacobian estimate is used outside its own box (BB p. 405 radius ). -/
theorem chart_box_scalar_upper_bound {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (w : ι → ℕ) (D : ℕ) (hw : ∀ i, w i ≤ D) (B : ι)
    {a b r K : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) (hr : 0 ≤ r) (hK : 0 ≤ K) :
    K * |lam B| * (a * (r / b)) ^ w B ≤
      (K * (1 / b) ^ D) * volumePolynomial lam w r := by
  have hab : a / b ≤ 1 / b := div_le_div_of_nonneg_right ha1 hb.le
  have hbinv : 1 ≤ 1 / b := (le_div_iff₀ hb).mpr (by simpa using hb1)
  have hp : (a / b) ^ w B ≤ (1 / b) ^ D :=
    (pow_le_pow_left₀ (div_nonneg ha hb.le) hab _).trans (pow_le_pow_right₀ hbinv (hw B))
  have hsingle : |lam B| * r ^ w B ≤ volumePolynomial lam w r :=
    Finset.single_le_sum (fun C _ => mul_nonneg (abs_nonneg _) (pow_nonneg hr _))
      (Finset.mem_univ B)
  calc
    _ = (K * (a / b) ^ w B) * (|lam B| * r ^ w B) := by
      have he : a * (r / b) = (a / b) * r := by ring
      rw [he, mul_pow]
      ring
    _ ≤ (K * (1 / b) ^ D) * (|lam B| * r ^ w B) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hK)
        (mul_nonneg (abs_nonneg _) (pow_nonneg hr _))
    _ ≤ _ := mul_le_mul_of_nonneg_left hsingle
      (mul_nonneg hK (pow_nonneg (div_nonneg zero_le_one hb.le) _))

end RothschildStein.G4

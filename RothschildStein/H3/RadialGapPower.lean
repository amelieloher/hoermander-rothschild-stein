-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.RadialProductBound
public import RothschildStein.H3.RadialWordWeight
public import RothschildStein.H3.RadialTermDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- The profile and gauge-product gap powers combine to the input's
 total weighted order. -/
theorem radial_gap_power_identity {a : ℝ} (ha : 0 < a) (j W : ℕ) :
    (2/a)^j * a^((j : ℝ)-(W : ℝ)) = 2^j * a^(-(W : ℝ)) := by
  calc
    (2/a)^j * a^((j : ℝ)-(W : ℝ)) =
        2^j * (a^((j : ℝ)))⁻¹ * a^((j : ℝ)-(W : ℝ)) := by
      rw [div_pow,Real.rpow_natCast]
      ring
    _ = 2^j * (a^(-(j : ℝ))*a^((j : ℝ)-(W : ℝ))) := by
      rw [Real.rpow_neg ha.le]
      ring
    _ = 2^j * a^(-(W : ℝ)) := by
      rw [← Real.rpow_add ha]
      congr 2
      ring

/-- One radial term has the exact uniform gap-power bound.
 The only analytic inputs are the profile and gauge derivative bounds. -/
theorem radialTerm_abs_bound {n m : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (ν : (Fin n → ℝ) → ℝ)
    (F : ℝ → ℝ) (w : Fin m → ℕ+) (M : List (Fin m) → ℝ)
    (t : ℕ × List (List (Fin m))) (x : Fin n → ℝ) {a κ : ℝ}
    (ha : 0 < a) (hav : a ≤ ν x) (hκ : 0 ≤ κ)
    (hcount : t.1 = t.2.length) (hne : ∀ K ∈ t.2, K ≠ [])
    (hM : ∀ K ∈ t.2, 0 ≤ M K)
    (hg : ∀ K ∈ t.2, |wordDerivative X K ν x| ≤ M K * (ν x)^(1-(wordWeight w K : ℝ)))
    (hp : |iteratedDeriv t.1 F (ν x)| ≤ κ*(2/a)^t.1) :
    |radialTermValue X ν F t x| ≤ (κ*2^t.1*(t.2.map M).prod)*
      a^(-((t.2.map (wordWeight w)).sum : ℝ)) := by
  have hv : 0 < ν x := ha.trans_le hav
  have hMprod : 0 ≤ (t.2.map M).prod := List.prod_nonneg (by
    intro b hb
    obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hb
    exact hM K hK)
  have hdeg : (t.2.length : ℝ)-((t.2.map (wordWeight w)).sum : ℝ) ≤ 0 := by
    apply sub_nonpos.mpr
    exact_mod_cast radial_factors_length_le_weight w t.2 hne
  have hpow := Real.rpow_le_rpow_of_nonpos ha hav hdeg
  have hproduct := (radialGaugeProduct_abs_bound X ν w M t.2 x hv hM hg).trans
    (mul_le_mul_of_nonneg_left hpow hMprod)
  calc
    |radialTermValue X ν F t x| =
        |iteratedDeriv t.1 F (ν x)| *|radialGaugeProduct X ν t.2 x| := by
      rw [radialTermValue,abs_mul]
    _ ≤ (κ*(2/a)^t.1)*((t.2.map M).prod*
        a^((t.2.length : ℝ)-((t.2.map (wordWeight w)).sum : ℝ))) :=
      mul_le_mul hp hproduct (abs_nonneg _) (mul_nonneg hκ (pow_nonneg (by positivity) _))
    _ = (κ*(t.2.map M).prod)*((2/a)^t.1*
        a^((t.1 : ℝ)-((t.2.map (wordWeight w)).sum : ℝ))) := by
      rw [hcount]
      ring
    _ = _ := by
      rw [radial_gap_power_identity ha]
      ring

end RothschildStein.H3

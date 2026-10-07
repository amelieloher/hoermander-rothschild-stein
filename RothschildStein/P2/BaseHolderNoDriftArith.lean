-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# No drift: the real arithmetic of the base Hölder estimate

The polynomial `K(g) = Λ (B₀ g⁻¹ + 2 B₁ g⁻² c_n + C₃ (2 + 2 b₁ g⁻¹ c_n + b₂ g⁻²) B₂ g⁻³ + 1)` of the cutoff step with
`c_n ≤ κ g^{-γ}` is bounded by `Λ K₀ g^{-(4 + γ)}` for `g ≤ 1` (all monomials are dominated by the top power
`E^{4+γ}`, `E = g⁻¹ ≥ 1`), and `g = (s - t)/3` converts `g^{-β}` into `3^β (s - t)^{-β}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
namespace RothschildStein.P2

/-- `E^k ≤ E^β` for `E ≥ 1` and `k ≤ β`. -/
theorem pow_le_rpow_of_le_exponent {E : ℝ} (hE : 1 ≤ E) {k : ℕ} {β : ℝ} (hk : (k : ℝ) ≤ β) :
    E ^ k ≤ E ^ β := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hE hk

/-- `E^k * E^γ ≤ E^β` for `E ≥ 1` and `k + γ ≤ β`. -/
theorem pow_mul_rpow_le {E : ℝ} (hE : 1 ≤ E) {k : ℕ} {γ β : ℝ} (hk : (k : ℝ) + γ ≤ β) :
    E ^ k * E ^ γ ≤ E ^ β := by
  have hE0 : 0 < E := lt_of_lt_of_le one_pos hE
  rw [← Real.rpow_natCast, ← Real.rpow_add hE0]
  exact Real.rpow_le_rpow_of_exponent_le hE hk

/-- The polynomial of the cutoff step is dominated by the top power `E^{4+γ}`. -/
theorem cutoffStep_poly_le {E γ κ cn Λ B₀ B₁ B₂ b₁ b₂ C₃ : ℝ} (hγ : 1 < γ) (hE : 1 ≤ E)
    (hcn0 : 0 ≤ cn) (hcn : cn ≤ κ * E ^ γ) (hΛ : 0 ≤ Λ) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hB₂ : 0 ≤ B₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hC₃ : 0 ≤ C₃) :
    Λ * (B₀ * E + 2 * (B₁ * E ^ 2) * cn +
        C₃ * (2 + 2 * (b₁ * E) * cn + b₂ * E ^ 2) * (B₂ * E ^ 3) + 1) ≤
      Λ * (B₀ + 2 * B₁ * κ + C₃ * B₂ * (2 + 2 * b₁ * κ + b₂) + 1) * E ^ (4 + γ) := by
  have hE0 : 0 < E := lt_of_lt_of_le one_pos hE
  have hκ : 0 ≤ κ := by
    have hEγ : 0 < E ^ γ := Real.rpow_pos_of_pos hE0 γ
    by_contra h
    have h' : κ < 0 := not_le.1 h
    have : κ * E ^ γ < 0 := mul_neg_of_neg_of_pos h' hEγ
    linarith
  set P : ℝ := E ^ (4 + γ) with hP
  have hP1 : 1 ≤ P := by
    rw [hP]
    exact Real.one_le_rpow hE (by linarith)
  have p1 : E ^ 1 ≤ P := by
    rw [hP]
    exact pow_le_rpow_of_le_exponent hE (by norm_num; linarith)
  have p3 : E ^ 3 ≤ P := by
    rw [hP]
    exact pow_le_rpow_of_le_exponent hE (by norm_num; linarith)
  have p5 : E ^ 5 ≤ P := by
    rw [hP]
    exact pow_le_rpow_of_le_exponent hE (by norm_num; linarith)
  have p2g : E ^ 2 * E ^ γ ≤ P := by
    rw [hP]
    exact pow_mul_rpow_le hE (by norm_num)
  have p4g : E ^ 4 * E ^ γ ≤ P := by
    rw [hP]
    exact pow_mul_rpow_le hE (by norm_num)
  have hE2 : 0 ≤ E ^ 2 := by positivity
  have hE4 : 0 ≤ E ^ 4 := by positivity
  have hEγ0 : 0 ≤ E ^ γ := Real.rpow_nonneg hE0.le γ
  -- the monomials
  have m1 : B₀ * E ≤ B₀ * P := mul_le_mul_of_nonneg_left (by simpa using p1) hB₀
  have m2 : 2 * (B₁ * E ^ 2) * cn ≤ 2 * B₁ * κ * P := by
    calc 2 * (B₁ * E ^ 2) * cn ≤ 2 * (B₁ * E ^ 2) * (κ * E ^ γ) :=
          mul_le_mul_of_nonneg_left hcn (by positivity)
      _ = 2 * B₁ * κ * (E ^ 2 * E ^ γ) := by ring
      _ ≤ 2 * B₁ * κ * P := mul_le_mul_of_nonneg_left p2g (by positivity)
  have m3a : 2 * C₃ * B₂ * E ^ 3 ≤ 2 * C₃ * B₂ * P :=
    mul_le_mul_of_nonneg_left p3 (by positivity)
  have m3b : 2 * C₃ * B₂ * b₁ * (E ^ 4 * cn) ≤ 2 * C₃ * B₂ * b₁ * κ * P := by
    calc 2 * C₃ * B₂ * b₁ * (E ^ 4 * cn) ≤ 2 * C₃ * B₂ * b₁ * (E ^ 4 * (κ * E ^ γ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcn hE4) (by positivity)
      _ = 2 * C₃ * B₂ * b₁ * κ * (E ^ 4 * E ^ γ) := by ring
      _ ≤ 2 * C₃ * B₂ * b₁ * κ * P := mul_le_mul_of_nonneg_left p4g (by positivity)
  have m3c : C₃ * B₂ * b₂ * E ^ 5 ≤ C₃ * B₂ * b₂ * P :=
    mul_le_mul_of_nonneg_left p5 (by positivity)
  have eq3 : C₃ * (2 + 2 * (b₁ * E) * cn + b₂ * E ^ 2) * (B₂ * E ^ 3) =
      2 * C₃ * B₂ * E ^ 3 + 2 * C₃ * B₂ * b₁ * (E ^ 4 * cn) + C₃ * B₂ * b₂ * E ^ 5 := by ring
  rw [eq3]
  have hsum : B₀ * E + 2 * (B₁ * E ^ 2) * cn +
        (2 * C₃ * B₂ * E ^ 3 + 2 * C₃ * B₂ * b₁ * (E ^ 4 * cn) + C₃ * B₂ * b₂ * E ^ 5) + 1 ≤
      (B₀ + 2 * B₁ * κ + C₃ * B₂ * (2 + 2 * b₁ * κ + b₂) + 1) * P := by
    linarith [m1, m2, m3a, m3b, m3c, hP1]
  exact mul_le_mul_of_nonneg_left hsum hΛ |>.trans_eq (by ring)

/-- With `g = (s - t)/3`, `(g⁻¹)^β = 3^β (s - t)^{-β}`. -/
theorem inv_div_three_rpow {s t β : ℝ} (hst : t < s) :
    (((s - t) / 3)⁻¹) ^ β = 3 ^ β * (s - t) ^ (-β) := by
  have h0 : 0 < s - t := sub_pos.2 hst
  have hne : s - t ≠ 0 := h0.ne'
  have e : ((s - t) / 3)⁻¹ = 3 * (s - t)⁻¹ := by field_simp
  rw [e, Real.mul_rpow (by norm_num) (inv_nonneg.2 h0.le), Real.inv_rpow h0.le, Real.rpow_neg h0.le]

end RothschildStein.P2

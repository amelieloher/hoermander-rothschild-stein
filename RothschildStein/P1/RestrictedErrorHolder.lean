-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RestrictedErrorSlice

/-!
# Restricted-error bounds: the Hölder estimate

For `x, x' ∈ S` and `h = dr x x'`, split the input integral at distance `2h` from `x'`
(BB pp. 606–607). The near part `{dr x' · ≤ 2h}` contributes `O(h) ‖f‖_∞`
(ball integrals about `x'` and, by the triangle inequality, about `x`, at radius `3h`). The far
part is covered by at most `J` dyadic shells `{2^j 2h ≤ dr x' · < 2^{j+1} 2h}`, each contributing
`O(h) ‖f‖_∞` by the kernel difference bound, where `2^J 2h ≥ 2ρ` and `J = ⌈log₂ (ρ / h)⌉`. Then
`h (1 + J) ≤ C ρ^(1-α) h^α`, using boundedness of `z^(1-α) (1 + |log z|)` on `(0, 1]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RothschildStein.P1

/-- `ρ / h ≤ 2^J` for `J = ⌈log₂ (ρ / h)⌉`. -/
theorem le_two_pow_ceil_logb {ρ h : ℝ} (hρ : 0 < ρ) (hh : 0 < h) :
    ρ / h ≤ 2 ^ ⌈Real.logb 2 (ρ / h)⌉₊ := by
  have hz : 0 < ρ / h := div_pos hρ hh
  calc ρ / h = (2 : ℝ) ^ Real.logb 2 (ρ / h) := (Real.rpow_logb two_pos (by norm_num) hz).symm
    _ ≤ (2 : ℝ) ^ (⌈Real.logb 2 (ρ / h)⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil _)
    _ = 2 ^ ⌈Real.logb 2 (ρ / h)⌉₊ := Real.rpow_natCast _ _

/-- The number of dyadic shells times the scale:
`h ⌈log₂ (ρ / h)⌉ ≤ (1 + 4 / (1 - α)) ρ^(1-α) h^α`, i.e. `z^(1-α) (1 + |log z|)` is bounded on
`(0, 1]`. -/
theorem mul_ceil_logb_le {ρ h α : ℝ} (hρ : 0 < ρ) (hh : 0 < h) (hα1 : α < 1) :
    h * (⌈Real.logb 2 (ρ / h)⌉₊ : ℝ) ≤ (1 + 4 / (1 - α)) * ρ ^ (1 - α) * h ^ α := by
  have hα' : 0 < 1 - α := by linarith
  have hpos : 0 ≤ (1 + 4 / (1 - α)) * ρ ^ (1 - α) * h ^ α := by positivity
  rcases le_or_gt ρ h with hρh | hρh
  · have hz : ρ / h ≤ 1 := (div_le_one hh).mpr hρh
    have h0 : ⌈Real.logb 2 (ρ / h)⌉₊ = 0 :=
      Nat.ceil_eq_zero.mpr (Real.logb_nonpos one_lt_two (div_pos hρ hh).le hz)
    rw [h0]
    simpa using hpos
  · set z := ρ / h with hz
    have hz1 : 1 < z := (one_lt_div hh).mpr hρh
    set ε : ℝ := (1 - α) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hlogz : Real.log z ≤ z ^ ε / ε := Real.log_le_rpow_div (by linarith) hε0
    have hlogb : Real.logb 2 z ≤ 4 / (1 - α) * z ^ ε := by
      rw [Real.logb]
      have hz0 : 0 ≤ z ^ ε := by positivity
      calc Real.log z / Real.log 2 ≤ (z ^ ε / ε) / (1 / 2) := by
            apply div_le_div₀ (by positivity) hlogz (by norm_num) hlog2
        _ = 4 / (1 - α) * z ^ ε := by rw [hε]; field_simp; ring
    have hJ : (⌈Real.logb 2 z⌉₊ : ℝ) < Real.logb 2 z + 1 :=
      Nat.ceil_lt_add_one (Real.logb_nonneg one_lt_two hz1.le)
    have hzε : 1 ≤ z ^ ε := Real.one_le_rpow hz1.le hε0.le
    have hJ' : (⌈Real.logb 2 z⌉₊ : ℝ) ≤ (1 + 4 / (1 - α)) * z ^ ε := by
      have h4 : 0 ≤ 4 / (1 - α) := by positivity
      nlinarith
    -- `h z^ε ≤ ρ^(1-α) h^α`
    have hpε : 0 < h ^ ε := Real.rpow_pos_of_pos hh ε
    have hkey : h * z ^ ε ≤ ρ ^ (1 - α) * h ^ α := by
      have e1 : h * z ^ ε = ρ ^ ε * h ^ (1 - ε) := by
        rw [hz, Real.div_rpow hρ.le hh.le, Real.rpow_sub hh, Real.rpow_one]
        field_simp
      have e2 : h ^ (1 - ε) = h ^ α * h ^ ε := by
        rw [← Real.rpow_add hh]
        congr 1
        rw [hε]
        ring
      have e3 : ρ ^ (1 - α) = ρ ^ ε * ρ ^ ε := by
        rw [← Real.rpow_add hρ]
        congr 1
        rw [hε]
        ring
      have hle : h ^ ε ≤ ρ ^ ε := Real.rpow_le_rpow hh.le hρh.le hε0.le
      rw [e1, e2, e3]
      have hρε : 0 ≤ ρ ^ ε := by positivity
      have hhα : 0 ≤ h ^ α := by positivity
      calc ρ ^ ε * (h ^ α * h ^ ε) ≤ ρ ^ ε * (h ^ α * ρ ^ ε) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hhα) hρε
        _ = ρ ^ ε * ρ ^ ε * h ^ α := by ring
    calc h * (⌈Real.logb 2 z⌉₊ : ℝ) ≤ h * ((1 + 4 / (1 - α)) * z ^ ε) :=
          mul_le_mul_of_nonneg_left hJ' hh.le
      _ = (1 + 4 / (1 - α)) * (h * z ^ ε) := by ring
      _ ≤ (1 + 4 / (1 - α)) * (ρ ^ (1 - α) * h ^ α) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (1 + 4 / (1 - α)) * ρ ^ (1 - α) * h ^ α := by ring

/-- For `0 < h < 2ρ`: `h ≤ 2 ρ^(1-α) h^α`. -/
theorem le_two_mul_rpow {ρ h α : ℝ} (hρ : 0 < ρ) (hh : 0 < h) (h2 : h < 2 * ρ) (hα0 : 0 < α)
    (hα1 : α < 1) : h ≤ 2 * ρ ^ (1 - α) * h ^ α := by
  have hα' : 0 < 1 - α := by linarith
  have e1 : h = h ^ α * h ^ (1 - α) := by
    rw [← Real.rpow_add hh]
    simp
  have h1 : h ^ (1 - α) ≤ (2 * ρ) ^ (1 - α) := Real.rpow_le_rpow hh.le h2.le hα'.le
  have h2' : (2 : ℝ) ^ (1 - α) ≤ 2 := by
    calc (2 : ℝ) ^ (1 - α) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = 2 := Real.rpow_one 2
  rw [Real.mul_rpow (by norm_num) hρ.le] at h1
  have hρ' : 0 ≤ ρ ^ (1 - α) := by positivity
  have hα'' : 0 ≤ h ^ α := by positivity
  calc h = h ^ α * h ^ (1 - α) := e1
    _ ≤ h ^ α * (2 ^ (1 - α) * ρ ^ (1 - α)) := mul_le_mul_of_nonneg_left h1 hα''
    _ ≤ h ^ α * (2 * ρ ^ (1 - α)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2' hρ') hα''
    _ = 2 * ρ ^ (1 - α) * h ^ α := by ring

/-- The Hölder constant `C_α = (10 A + B (1 + 4 / (1 - α))) Cv 2^(q+1)`
of the restricted-error Hölder bound. -/
def holderConst (A B Cv : ℝ) (q : ℕ) (α : ℝ) : ℝ :=
  (10 * A + B * (1 + 4 / (1 - α))) * (Cv * 2 ^ (q + 1))

namespace SliceBounds

variable {E : Type*} [MeasurableSpace E] {μ : MeasureTheory.Measure E} {S : Set E}
  {dr : E → E → ℝ} {q : ℕ} {ρ Cv : ℝ} {K : E → E → ℝ} {A B : ℝ}
  (hS : ShellData μ S dr q ρ Cv) (hK : SliceBounds S dr q K A B) {x x' : E}

include hS hK

/-- **Near/far splitting**: for `x, x' ∈ S`, `h = dr x x'`, and `J`
dyadic shells covering `S` about `x'` beyond `2h` (`2^J 2h > dr x' y` on `S`),
`|𝓕 f x - 𝓕 f x'| ≤ M (5 A C h + J B h C)` with `C = Cv 2^(q+1)` and `|f| ≤ M` on `S`. -/
theorem abs_sub_le_near_far {f : E → ℝ} (hf : AEStronglyMeasurable f (μ.restrict S)) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ y ∈ S, |f y| ≤ M) (hx : x ∈ S) (hx' : x' ∈ S) {J : ℕ}
    (hJ : 0 < dr x x' → ∀ y ∈ S, dr x' y < 2 ^ J * (2 * dr x x')) :
    |∫ y in S, K x y * f y ∂μ - ∫ y in S, K x' y * f y ∂μ| ≤
      M * (5 * A * (Cv * 2 ^ (q + 1)) * dr x x' +
        J * (B * dr x x') * (Cv * 2 ^ (q + 1))) := by
  set h := dr x x' with hh
  set C₁ : ℝ := Cv * 2 ^ (q + 1) with hC₁
  have hh0 : 0 ≤ h := hS.dr_nonneg x hx x' hx'
  have hC₁0 : 0 ≤ C₁ := mul_nonneg hS.Cv_nonneg (by positivity)
  have hA := hK.A_nonneg
  have hB := hK.B_nonneg
  set N : Set E := S ∩ {y | dr x' y ≤ 2 * h} with hN
  have hNm : MeasurableSet N := hS.measurableSet_closedBall hx' _
  have hNS : N ⊆ S := inter_subset_left
  have hix := hK.integrable_row hS hf hM0 hM hx
  have hix' := hK.integrable_row hS hf hM0 hM hx'
  have e1 : ∫ y in S, K x y * f y ∂μ =
      ∫ y in N, K x y * f y ∂μ + ∫ y in S \ N, K x y * f y ∂μ := by
    have := integral_inter_add_sdiff (f := fun y => K x y * f y) (s := S) (t := N) (μ := μ) hNm hix
    rw [inter_eq_right.mpr hNS] at this
    exact this.symm
  have e2 : ∫ y in S, K x' y * f y ∂μ =
      ∫ y in N, K x' y * f y ∂μ + ∫ y in S \ N, K x' y * f y ∂μ := by
    have := integral_inter_add_sdiff (f := fun y => K x' y * f y) (s := S) (t := N) (μ := μ) hNm
      hix'
    rw [inter_eq_right.mpr hNS] at this
    exact this.symm
  have e3 : ∫ y in S \ N, (K x y * f y - K x' y * f y) ∂μ =
      ∫ y in S \ N, K x y * f y ∂μ - ∫ y in S \ N, K x' y * f y ∂μ :=
    integral_sub (IntegrableOn.mono_set (hix : IntegrableOn _ S μ) sdiff_subset)
      (IntegrableOn.mono_set (hix' : IntegrableOn _ S μ) sdiff_subset)
  have hsplit : ∫ y in S, K x y * f y ∂μ - ∫ y in S, K x' y * f y ∂μ =
      ((∫ y in N, K x y * f y ∂μ) - ∫ y in N, K x' y * f y ∂μ) +
        ∫ y in S \ N, (K x y * f y - K x' y * f y) ∂μ := by
    rw [e1, e2, e3]
    ring
  -- the near integrals
  have hI1 : |∫ y in N, K x y * f y ∂μ| ≤ A * M * C₁ * (3 * h) := by
    have h1 := ofReal_abs_integral_le (fun y => K x y * f y) (μ.restrict N)
    have hnn : 0 ≤ A * M * C₁ * (3 * h) := by positivity
    have h2 : ∫⁻ y in N, ‖K x y * f y‖ₑ ∂μ ≤ ENNReal.ofReal (A * M * C₁ * (3 * h)) := by
      calc ∫⁻ y in N, ‖K x y * f y‖ₑ ∂μ
          ≤ ∫⁻ y in N, ENNReal.ofReal (A * M / dr x y ^ q) ∂μ :=
            setLIntegral_mono' hNm fun y hy => hK.enorm_mul_le hS hx (hNS hy) (hM y (hNS hy))
        _ ≤ ∫⁻ y in S ∩ {y | dr x y ≤ 3 * h}, ENNReal.ofReal (A * M / dr x y ^ q) ∂μ := by
            refine lintegral_mono_set fun y hy => ⟨hy.1, ?_⟩
            have h3 : dr x y ≤ dr x x' + dr x' y := hS.dr_tri x hx x' hx' y hy.1
            have h4 : dr x' y ≤ 2 * h := hy.2
            show dr x y ≤ 3 * h
            linarith
        _ ≤ ENNReal.ofReal (A * M * C₁ * (3 * h)) :=
            hS.lintegral_ball_le hx (mul_nonneg hA hM0) (by positivity)
    exact (ENNReal.ofReal_le_ofReal_iff hnn).mp (h1.trans h2)
  have hI2 : |∫ y in N, K x' y * f y ∂μ| ≤ A * M * C₁ * (2 * h) := by
    have h1 := ofReal_abs_integral_le (fun y => K x' y * f y) (μ.restrict N)
    have hnn : 0 ≤ A * M * C₁ * (2 * h) := by positivity
    have h2 : ∫⁻ y in N, ‖K x' y * f y‖ₑ ∂μ ≤ ENNReal.ofReal (A * M * C₁ * (2 * h)) := by
      calc ∫⁻ y in N, ‖K x' y * f y‖ₑ ∂μ
          ≤ ∫⁻ y in N, ENNReal.ofReal (A * M / dr x' y ^ q) ∂μ :=
            setLIntegral_mono' hNm fun y hy => hK.enorm_mul_le hS hx' (hNS hy) (hM y (hNS hy))
        _ ≤ ENNReal.ofReal (A * M * C₁ * (2 * h)) :=
            hS.lintegral_ball_le hx' (mul_nonneg hA hM0) (by positivity)
    exact (ENNReal.ofReal_le_ofReal_iff hnn).mp (h1.trans h2)
  -- the far integral
  have hI3 : |∫ y in S \ N, (K x y * f y - K x' y * f y) ∂μ| ≤ M * (J * (B * h) * C₁) := by
    have h1 := ofReal_abs_integral_le (fun y => K x y * f y - K x' y * f y) (μ.restrict (S \ N))
    have hnn : 0 ≤ M * (J * (B * h) * C₁) := by positivity
    have hpt : ∀ y ∈ S \ N, ‖K x y * f y - K x' y * f y‖ₑ ≤
        ENNReal.ofReal (M * B * h / dr x' y ^ (q + 1)) := by
      intro y hy
      have hy2 : 2 * h < dr x' y := by
        by_contra hc
        exact hy.2 ⟨hy.1, not_lt.mp hc⟩
      have hd : |K x' y - K x y| ≤ B * h / dr x' y ^ (q + 1) := hK.diff x hx x' hx' y hy.1 hy2
      rw [← sub_mul, enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
        ← ENNReal.ofReal_mul (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      calc |K x y - K x' y| * |f y| ≤ (B * h / dr x' y ^ (q + 1)) * M :=
            mul_le_mul (by rw [abs_sub_comm]; exact hd) (hM y hy.1) (abs_nonneg _)
              (by have := hS.dr_nonneg x' hx' y hy.1; positivity)
        _ = M * B * h / dr x' y ^ (q + 1) := by ring
    have h2 : ∫⁻ y in S \ N, ‖K x y * f y - K x' y * f y‖ₑ ∂μ ≤
        ENNReal.ofReal (M * (J * (B * h) * C₁)) := by
      refine (setLIntegral_mono' (hS.measurableSet.diff hNm) hpt).trans ?_
      by_cases hpos : 0 < h
      · calc ∫⁻ y in S \ N, ENNReal.ofReal (M * B * h / dr x' y ^ (q + 1)) ∂μ
            ≤ ∫⁻ y in S ∩ {y | 2 * h ≤ dr x' y},
                ENNReal.ofReal (M * B * h / dr x' y ^ (q + 1)) ∂μ := by
              refine lintegral_mono_set fun y hy => ⟨hy.1, ?_⟩
              show 2 * h ≤ dr x' y
              by_contra hc
              exact hy.2 ⟨hy.1, show dr x' y ≤ 2 * h from (not_le.mp hc).le⟩
          _ ≤ ENNReal.ofReal (J * (M * B * h * C₁)) :=
              hS.lintegral_far_le hx' (by positivity) (by positivity) J (hJ hpos)
          _ = ENNReal.ofReal (M * (J * (B * h) * C₁)) := by congr 1; ring
      · have hz : h = 0 := le_antisymm (not_lt.mp hpos) hh0
        rw [hz]
        simp
    exact (ENNReal.ofReal_le_ofReal_iff hnn).mp (h1.trans h2)
  rw [hsplit]
  calc |(∫ y in N, K x y * f y ∂μ - ∫ y in N, K x' y * f y ∂μ) +
        ∫ y in S \ N, (K x y * f y - K x' y * f y) ∂μ|
      ≤ |∫ y in N, K x y * f y ∂μ - ∫ y in N, K x' y * f y ∂μ| +
        |∫ y in S \ N, (K x y * f y - K x' y * f y) ∂μ| := abs_add_le _ _
    _ ≤ (|∫ y in N, K x y * f y ∂μ| + |∫ y in N, K x' y * f y ∂μ|) +
        |∫ y in S \ N, (K x y * f y - K x' y * f y) ∂μ| := by
        gcongr
        exact abs_sub _ _
    _ ≤ A * M * C₁ * (3 * h) + A * M * C₁ * (2 * h) + M * (J * (B * h) * C₁) := by
        linarith [hI1, hI2, hI3]
    _ = M * (5 * A * C₁ * h + J * (B * h) * C₁) := by ring

/-- **The Hölder bound** for the restricted error: for `x, x' ∈ S`,
`0 < α < 1`, `|f| ≤ M` on `S`,
`|𝓕 f x - 𝓕 f x'| ≤ C_α ρ^(1-α) M dr(x, x')^α`. -/
theorem abs_sub_le_holder {f : E → ℝ} (hf : AEStronglyMeasurable f (μ.restrict S)) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ y ∈ S, |f y| ≤ M) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hx : x ∈ S) (hx' : x' ∈ S) :
    |∫ y in S, K x y * f y ∂μ - ∫ y in S, K x' y * f y ∂μ| ≤
      holderConst A B Cv q α * ρ ^ (1 - α) * M * dr x x' ^ α := by
  have hh0 := hS.dr_nonneg x hx x' hx'
  have hh2 := hS.dr_lt x hx x' hx'
  have hA := hK.A_nonneg
  have hB := hK.B_nonneg
  have hC₁0 : 0 ≤ Cv * 2 ^ (q + 1) := mul_nonneg hS.Cv_nonneg (by positivity)
  rcases hh0.eq_or_lt with hz | hpos
  · have := hK.abs_sub_le_near_far hS hf hM0 hM hx hx' (J := 0)
      (fun hp => absurd hp (by rw [← hz]; exact lt_irrefl _))
    rw [← hz] at this ⊢
    rw [Real.zero_rpow hα0.ne', mul_zero]
    simpa using this
  · set h := dr x x' with hh
    set J : ℕ := ⌈Real.logb 2 (ρ / h)⌉₊ with hJdef
    have hJ := le_two_pow_ceil_logb hS.ρ_pos hpos
    have hJ' : ∀ y ∈ S, dr x' y < 2 ^ J * (2 * h) := by
      intro y hy
      calc dr x' y < 2 * ρ := hS.dr_lt x' hx' y hy
        _ = ρ / h * (2 * h) := by field_simp
        _ ≤ 2 ^ J * (2 * h) := mul_le_mul_of_nonneg_right hJ (by positivity)
    have h1 := hK.abs_sub_le_near_far hS hf hM0 hM hx hx' (J := J) (fun _ => hJ')
    have e1 := le_two_mul_rpow hS.ρ_pos hpos hh2 hα0 hα1
    have e2 := mul_ceil_logb_le hS.ρ_pos hpos hα1
    have h5A : 0 ≤ 5 * A := by positivity
    calc _ ≤ M * (5 * A * (Cv * 2 ^ (q + 1)) * h + J * (B * h) * (Cv * 2 ^ (q + 1))) := h1
      _ = M * (Cv * 2 ^ (q + 1)) * (5 * A * h + B * (h * J)) := by ring
      _ ≤ M * (Cv * 2 ^ (q + 1)) * (5 * A * (2 * ρ ^ (1 - α) * h ^ α) +
            B * ((1 + 4 / (1 - α)) * ρ ^ (1 - α) * h ^ α)) :=
          mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left e1 h5A)
            (mul_le_mul_of_nonneg_left e2 hB)) (mul_nonneg hM0 hC₁0)
      _ = holderConst A B Cv q α * ρ ^ (1 - α) * M * h ^ α := by unfold holderConst; ring

end SliceBounds

end RothschildStein.P1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiThresholdSummability

/-! # Rational nesting parameters for logarithmic iteration

The parameter sequence approaches a fixed interior scale. Its adjacent gaps decay
quadratically in the index, so the logarithmic nesting costs grow at most
logarithmically. The resulting thresholds are summable with the contraction weights.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace HeatKernel

/-- Increasing parameters approaching a fixed interior outer scale. -/
def bombieriGiustiNestingParameter (θ σ : ℝ) (j : ℕ) : ℝ :=
  θ + (σ - θ) * (1 - 1 / ((j : ℝ) + 1))

/-- The exact gap between two successive nesting parameters. -/
def bombieriGiustiNestingGap (d : ℝ) (j : ℕ) : ℝ :=
  d / (((j : ℝ) + 1) * ((j : ℝ) + 2))

/-- The logarithmic cost corresponding to a quadratic nesting gap. -/
def bombieriGiustiNestingCost (C κ d : ℝ) (j : ℕ) : ℝ :=
  Real.log C + κ * (Real.log ((j : ℝ) + 1) + Real.log ((j : ℝ) + 2) - Real.log d)

@[simp] theorem bombieriGiustiNestingParameter_zero (θ σ : ℝ) :
    bombieriGiustiNestingParameter θ σ 0 = θ := by
  simp [bombieriGiustiNestingParameter]

/-- Every nesting parameter lies between the initial and the fixed outer scale. -/
theorem bombieriGiustiNestingParameter_bounds {θ σ : ℝ} (hθσ : θ < σ) (j : ℕ) :
    θ ≤ bombieriGiustiNestingParameter θ σ j ∧
      bombieriGiustiNestingParameter θ σ j < σ := by
  have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have hinv : 1 / ((j : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr hj
  have hinvpos : 0 < 1 / ((j : ℝ) + 1) := by positivity
  dsimp [bombieriGiustiNestingParameter]
  constructor <;> nlinarith

/-- Successive parameter differences equal the displayed quadratic gap. -/
theorem bombieriGiustiNestingParameter_succ_sub (θ σ : ℝ) (j : ℕ) :
    bombieriGiustiNestingParameter θ σ (j + 1) - bombieriGiustiNestingParameter θ σ j =
      bombieriGiustiNestingGap (σ - θ) j := by
  dsimp [bombieriGiustiNestingParameter, bombieriGiustiNestingGap]
  push_cast
  have hj₁ : (j : ℝ) + 1 ≠ 0 := by positivity
  have hj₂ : (j : ℝ) + 1 + 1 ≠ 0 := by positivity
  have hj₂' : (j : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The gap is positive whenever the fixed outer scale is larger than the inner one. -/
theorem bombieriGiustiNestingGap_pos {d : ℝ} (hd : 0 < d) (j : ℕ) :
    0 < bombieriGiustiNestingGap d j := by
  dsimp [bombieriGiustiNestingGap]
  positivity

/-- The expanded nesting cost is exactly the cost of the adjacent parameter gap. -/
theorem bombieriGiustiNestingCost_eq_log_gap (C κ : ℝ) {d : ℝ} (hd : 0 < d) (j : ℕ) :
    bombieriGiustiNestingCost C κ d j =
      Real.log C + κ * Real.log (1 / bombieriGiustiNestingGap d j) := by
  have hj₁ : (j : ℝ) + 1 ≠ 0 := by positivity
  have hj₂ : (j : ℝ) + 2 ≠ 0 := by positivity
  have he : 1 / bombieriGiustiNestingGap d j =
      (((j : ℝ) + 1) * ((j : ℝ) + 2)) / d := by
    dsimp [bombieriGiustiNestingGap]
    field_simp
  rw [he, Real.log_div (mul_ne_zero hj₁ hj₂) hd.ne', Real.log_mul hj₁ hj₂]
  rfl

/-- The nesting cost is nonnegative for normalized geometric and mean-value data. -/
theorem bombieriGiustiNestingCost_nonneg {C κ d : ℝ}
    (hC : 1 ≤ C) (hκ : 0 ≤ κ) (hd : 0 ≤ d) (hd1 : d ≤ 1) (j : ℕ) :
    0 ≤ bombieriGiustiNestingCost C κ d j := by
  have hlogd : Real.log d ≤ 0 := Real.log_nonpos hd hd1
  have hj₁ : 0 ≤ Real.log ((j : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hj₂ : 0 ≤ Real.log ((j : ℝ) + 2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  exact add_nonneg (Real.log_nonneg hC) (mul_nonneg hκ (by linarith))

/-- The cost of each quadratic gap is bounded by a constant plus twice the
gap exponent times the logarithm of the shifted index. -/
theorem bombieriGiustiNestingCost_le_logarithmic (C d : ℝ) {κ : ℝ}
    (hκ : 0 ≤ κ) (j : ℕ) :
    bombieriGiustiNestingCost C κ d j ≤
      (Real.log C - κ * Real.log d) + (2 * κ) * Real.log ((j : ℝ) + 2) := by
  have hlog : Real.log ((j : ℝ) + 1) ≤ Real.log ((j : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have h := mul_le_mul_of_nonneg_left hlog hκ
  dsimp [bombieriGiustiNestingCost]
  nlinarith

/-- For the actual rational nesting parameters, logarithmic tail thresholds are
summable. The small-exponent scale may be four or eight, or any nonnegative value. -/
theorem summable_bombieriGiusti_thresholds_nesting
    {p₀ A C κ d s : ℝ} (hp₀ : 0 < p₀) (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hκ : 0 ≤ κ) (hd : 0 ≤ d) (hd1 : d ≤ 1) (hs : 0 ≤ s) :
    Summable (fun j => (3 / 4 : ℝ) ^ j * bombieriGiustiUniformThreshold p₀ A
      (s * (bombieriGiustiNestingCost C κ d j + Real.log 2 + 1))) := by
  have hconstant : 0 ≤ Real.log C - κ * Real.log d := by
    have hlogd := Real.log_nonpos hd hd1
    have hlogC := Real.log_nonneg hC
    have hprod := mul_nonpos_of_nonneg_of_nonpos hκ hlogd
    linarith
  exact summable_bombieriGiusti_thresholds_of_logarithmic_cost hp₀ hA hconstant hs
    (bombieriGiustiNestingCost_le_logarithmic C d hκ)

end HeatKernel

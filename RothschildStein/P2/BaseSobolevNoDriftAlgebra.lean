-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationAbsorb

/-!
# No drift: the arithmetic of the cutoff step and of the absorption

Real and `ℝ≥0∞` arithmetic of the base Sobolev estimate (BB pp. 586-587, (11.69)-(11.72)) in a no-drift alphabet:

* `second_scale_word_noDrift`: multiplication of the per-word bound of the cutoff step by `a² = (2h)²`
  (the three terms become `a² ‖f‖`, `a ‖Du‖`, `‖u‖`, BB (11.69)-(11.70));
* `second_scale_noDrift`: the same by `4 h²` for the sum over the `N` words of weight two, with
  `r² ‖f‖`, `h ‖Du‖`, `‖u‖`;
* `second_absorb_algebra_noDrift`: from `Φ₂ ≤ α F' + β Φ₁ + γ Φ₀` and `Φ₁ ≤ δ Φ₂ + C δ^{-1} Φ₀`, with
  `Φ₂ < ∞`, conclude `Φ₂ + Φ₁ ≤ K (F' + Φ₀)` (BB (11.71)-(11.72)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein

section Algebra

/-- Multiplication of the per-word bound of `second_step` by `a² = 4 h²`, `a = (1 - σ) r = 2 h`
(BB (11.69)-(11.70)): the three terms become `r² ‖f‖`, `h ‖Du‖` and `‖u‖` with constants independent of
`h ≤ r ≤ 1`. Here `N` is the number of words of weight two. -/
theorem second_scale_noDrift {q : ℕ} {h r Λ B : ℝ} (N : ℕ) (hh : 0 < h) (hhr : h ≤ r) (hr1 : r ≤ 1)
    (hΛ : 0 ≤ Λ) (hB : 0 ≤ B) {S F T1 N0 : ℝ≥0∞}
    (hS : S ≤ (N : ℝ≥0∞) * (ENNReal.ofReal Λ * (F + ENNReal.ofReal (2 * (B / h)) * T1 +
        (ENNReal.ofReal (((q : ℝ) + 1) * (B / h ^ 2)) + 1) * N0))) :
    ENNReal.ofReal (4 * h ^ 2) * S ≤
      ENNReal.ofReal (4 * ((N : ℝ) * Λ) * r ^ 2) * F +
        ENNReal.ofReal (8 * ((N : ℝ) * Λ) * B) * (ENNReal.ofReal h * T1) +
        ENNReal.ofReal (4 * ((N : ℝ) * Λ) * (((q : ℝ) + 1) * B + 1)) * N0 := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hh0 : h ≠ 0 := hh.ne'
  have c1 : ENNReal.ofReal (4 * h ^ 2) * (N : ℝ≥0∞) * ENNReal.ofReal Λ =
      ENNReal.ofReal (4 * h ^ 2 * N * Λ) := by
    rw [← ENNReal.ofReal_natCast N, ofReal_mul_ofReal _ (by positivity),
      ofReal_mul_ofReal _ (by positivity)]
  have c2 : ENNReal.ofReal (4 * h ^ 2) * (N : ℝ≥0∞) * ENNReal.ofReal Λ *
      ENNReal.ofReal (2 * (B / h)) = ENNReal.ofReal (8 * ((N : ℝ) * Λ) * B) * ENNReal.ofReal h := by
    rw [c1, ofReal_mul_ofReal _ (by positivity), ofReal_mul_ofReal _ (by positivity)]
    congr 1
    field_simp
    ring
  have c3 : ENNReal.ofReal (4 * h ^ 2) * (N : ℝ≥0∞) * ENNReal.ofReal Λ *
        ENNReal.ofReal (((q : ℝ) + 1) * (B / h ^ 2)) +
      ENNReal.ofReal (4 * h ^ 2) * (N : ℝ≥0∞) * ENNReal.ofReal Λ =
      ENNReal.ofReal (4 * ((N : ℝ) * Λ) * (((q : ℝ) + 1) * B + h ^ 2)) := by
    rw [c1, ofReal_mul_ofReal _ (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by positivity)]
    congr 1
    field_simp
  have hh2 : h ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hh.le hhr 2
  have hh2' : h ^ 2 ≤ 1 := by nlinarith
  have hNΛ : 0 ≤ (N : ℝ) * Λ := mul_nonneg hN hΛ
  calc ENNReal.ofReal (4 * h ^ 2) * S
      ≤ ENNReal.ofReal (4 * h ^ 2) * ((N : ℝ≥0∞) * (ENNReal.ofReal Λ * (F +
          ENNReal.ofReal (2 * (B / h)) * T1 +
          (ENNReal.ofReal (((q : ℝ) + 1) * (B / h ^ 2)) + 1) * N0))) := mul_le_mul' le_rfl hS
    _ = (ENNReal.ofReal (4 * h ^ 2) * (N : ℝ≥0∞) * ENNReal.ofReal Λ) * F +
        (ENNReal.ofReal (4 * h ^ 2) * (N : ℝ≥0∞) * ENNReal.ofReal Λ *
          ENNReal.ofReal (2 * (B / h))) * T1 +
        (ENNReal.ofReal (4 * h ^ 2) * (N : ℝ≥0∞) * ENNReal.ofReal Λ *
          ENNReal.ofReal (((q : ℝ) + 1) * (B / h ^ 2)) +
          ENNReal.ofReal (4 * h ^ 2) * (N : ℝ≥0∞) * ENNReal.ofReal Λ) * N0 := by ring
    _ = ENNReal.ofReal (4 * h ^ 2 * N * Λ) * F +
        ENNReal.ofReal (8 * ((N : ℝ) * Λ) * B) * (ENNReal.ofReal h * T1) +
        ENNReal.ofReal (4 * ((N : ℝ) * Λ) * (((q : ℝ) + 1) * B + h ^ 2)) * N0 := by
      rw [c2, c3, c1]
      ring
    _ ≤ _ := by
      refine add_le_add (add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl) le_rfl)
        (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      · have : 4 * h ^ 2 * N * Λ = 4 * ((N : ℝ) * Λ) * h ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hh2 (by positivity)
      · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **The absorption algebra** (BB (11.71)-(11.72)): from
`Φ₂ ≤ α F' + β Φ₁ + γ Φ₀` with `Φ₂ < ∞` and the interpolation `Φ₁ ≤ δ Φ₂ + C δ^{-1} Φ₀`
(`0 < δ ≤ δ₀`), choose `δ` with `β δ ≤ 1/2`; then `Φ₂ + Φ₁ ≤ K (F' + Φ₀)` with `K` depending only on
`α, β, γ, δ₀, C`. -/
theorem second_absorb_algebra_noDrift {α β γ δ₀ Cabs : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hδ₀ : 0 < δ₀) (hCabs : 0 ≤ Cabs) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ F' Φ₀ Φ₁ Φ₂ : ℝ≥0∞, Φ₂ ≠ ⊤ →
      Φ₂ ≤ ENNReal.ofReal α * F' + ENNReal.ofReal β * Φ₁ + ENNReal.ofReal γ * Φ₀ →
      (∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        Φ₁ ≤ ENNReal.ofReal δ * Φ₂ + ENNReal.ofReal (Cabs / δ) * Φ₀) →
      Φ₂ + Φ₁ ≤ ENNReal.ofReal K * (F' + Φ₀) := by
  have hβ1 : 0 < 2 * β + 1 := by linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min δ₀ (1 / (2 * β + 1)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact lt_min hδ₀ (by positivity)
  have hδδ₀ : δ ≤ δ₀ := by
    rw [hδdef]
    exact min_le_left _ _
  have hδβ : δ ≤ 1 / (2 * β + 1) := by
    rw [hδdef]
    exact min_le_right _ _
  have hβδ : β * δ ≤ 1 / 2 := by
    have h1 : β * δ ≤ β * (1 / (2 * β + 1)) := mul_le_mul_of_nonneg_left hδβ hβ
    have h2 : β * (1 / (2 * β + 1)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ hβ1 (by norm_num)]
      nlinarith
    linarith
  have hCδ : 0 ≤ Cabs / δ := div_nonneg hCabs hδ0.le
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = α + β * (Cabs / δ) + γ := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have := mul_nonneg hβ hCδ
    linarith
  refine ⟨(1 + δ) * 2 * M + Cabs / δ, by positivity, fun F' Φ₀ Φ₁ Φ₂ hfin h1 h2 => ?_⟩
  have h2' := h2 δ hδ0 hδδ₀
  have hA : Φ₂ ≤ (ENNReal.ofReal α * F' +
      (ENNReal.ofReal (β * (Cabs / δ)) + ENNReal.ofReal γ) * Φ₀) +
        ENNReal.ofReal (β * δ) * Φ₂ := by
    calc Φ₂ ≤ ENNReal.ofReal α * F' + ENNReal.ofReal β * Φ₁ + ENNReal.ofReal γ * Φ₀ := h1
      _ ≤ ENNReal.ofReal α * F' + ENNReal.ofReal β * (ENNReal.ofReal δ * Φ₂ +
          ENNReal.ofReal (Cabs / δ) * Φ₀) + ENNReal.ofReal γ * Φ₀ :=
        add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl h2')) le_rfl
      _ = _ := by
        rw [ENNReal.ofReal_mul hβ, ENNReal.ofReal_mul hβ]
        ring
  have h3 := ennreal_absorb hfin hβδ hA
  have h4 : Φ₂ + Φ₁ ≤ ENNReal.ofReal (1 + δ) * Φ₂ + ENNReal.ofReal (Cabs / δ) * Φ₀ := by
    calc Φ₂ + Φ₁ ≤ Φ₂ + (ENNReal.ofReal δ * Φ₂ + ENNReal.ofReal (Cabs / δ) * Φ₀) :=
          add_le_add le_rfl h2'
      _ = _ := by
        rw [ENNReal.ofReal_add zero_le_one hδ0.le, ENNReal.ofReal_one]
        ring
  have h5 : ENNReal.ofReal (1 + δ) * Φ₂ ≤ ENNReal.ofReal ((1 + δ) * 2 * M) * (F' + Φ₀) := by
    have hcoef : ENNReal.ofReal (β * (Cabs / δ)) + ENNReal.ofReal γ ≤ ENNReal.ofReal M := by
      rw [← ENNReal.ofReal_add (mul_nonneg hβ hCδ) hγ]
      exact ENNReal.ofReal_le_ofReal (by rw [hMdef]; linarith)
    have h2e : ENNReal.ofReal 2 = 2 := by simp
    have hαM : ENNReal.ofReal α ≤ ENNReal.ofReal M :=
      ENNReal.ofReal_le_ofReal (by
        rw [hMdef]
        have := mul_nonneg hβ hCδ
        linarith)
    calc ENNReal.ofReal (1 + δ) * Φ₂
        ≤ ENNReal.ofReal (1 + δ) * (2 * (ENNReal.ofReal α * F' +
          (ENNReal.ofReal (β * (Cabs / δ)) + ENNReal.ofReal γ) * Φ₀)) := mul_le_mul' le_rfl h3
      _ = ENNReal.ofReal ((1 + δ) * 2) * (ENNReal.ofReal α * F' +
          (ENNReal.ofReal (β * (Cabs / δ)) + ENNReal.ofReal γ) * Φ₀) := by
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 + δ by positivity), h2e]
        ring
      _ ≤ ENNReal.ofReal ((1 + δ) * 2) * (ENNReal.ofReal M * F' + ENNReal.ofReal M * Φ₀) :=
        mul_le_mul' le_rfl (add_le_add (mul_le_mul' hαM le_rfl) (mul_le_mul' hcoef le_rfl))
      _ = _ := by
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ (1 + δ) * 2 by positivity)]
        ring
  calc Φ₂ + Φ₁ ≤ ENNReal.ofReal (1 + δ) * Φ₂ + ENNReal.ofReal (Cabs / δ) * Φ₀ := h4
    _ ≤ ENNReal.ofReal ((1 + δ) * 2 * M) * (F' + Φ₀) +
        ENNReal.ofReal (Cabs / δ) * (F' + Φ₀) :=
      add_le_add h5 (mul_le_mul' le_rfl le_add_self)
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) hCδ]
      ring

end Algebra

end RothschildStein.P2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Ring.GeomSum

/-!
# The iteration lemma

BB p. 385, Lem 8.55, in a quantitative form. A bounded function
`ψ` on `[t₀, t₁]` with `ψ(t) ≤ θ ψ(s) + A (s - t)^{-β} + B` for all `t₀ ≤ t < s ≤ t₁` satisfies
`ψ(r) ≤ C (A (R - r)^{-β} + B)` for `t₀ ≤ r < R ≤ t₁`.

Proof: for a ratio `τ ∈ (0, 1)` with `θ τ^{-β} < 1` put
`t_j = r + (R - r)(1 - τ^j)`; then `t_{j+1} - t_j = (R - r) (1 - τ) τ^j` and `N` applications of
the hypothesis give
`ψ(r) ≤ θ^N ψ(t_N) + A (1 - τ)^{-β} (R - r)^{-β} ∑_{j<N} (θ τ^{-β})^j + B ∑_{j<N} θ^j`.
The first term tends to zero (`ψ` is bounded above), the two geometric series converge.
Nonnegativity of `ψ` is not used, only boundedness from above, so the statements are slightly
more general than the nonnegative case. The exponent `β ≥ 0` includes `β = 0` (any fixed `τ`, avoiding the
printed `1/β` expression); for `θ < 1/3` the constant depends on `β` alone
(`exists_iteration_third`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter Finset
open scoped Topology
namespace RothschildStein.P2

/-- The partition points `t_j = r + (R - r)(1 - τ^j)` of the iteration. -/
def iterationPoint (r R τ : ℝ) (j : ℕ) : ℝ := r + (R - r) * (1 - τ ^ j)

theorem iterationPoint_zero (r R τ : ℝ) : iterationPoint r R τ 0 = r := by
  simp [iterationPoint]

theorem iterationPoint_ge {r R τ : ℝ} (hrR : r ≤ R) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (j : ℕ) :
    r ≤ iterationPoint r R τ j := by
  unfold iterationPoint
  have : τ ^ j ≤ 1 := pow_le_one₀ hτ0 hτ1
  nlinarith [sub_nonneg.2 hrR]

theorem iterationPoint_lt {r R τ : ℝ} (hrR : r < R) (hτ0 : 0 < τ) (j : ℕ) :
    iterationPoint r R τ j < R := by
  unfold iterationPoint
  have : 0 < τ ^ j := pow_pos hτ0 j
  nlinarith [sub_pos.2 hrR]

theorem iterationPoint_succ_sub (r R τ : ℝ) (j : ℕ) :
    iterationPoint r R τ (j + 1) - iterationPoint r R τ j = (R - r) * (τ ^ j * (1 - τ)) := by
  unfold iterationPoint
  ring

theorem iterationPoint_lt_succ {r R τ : ℝ} (hrR : r < R) (hτ0 : 0 < τ) (hτ1 : τ < 1) (j : ℕ) :
    iterationPoint r R τ j < iterationPoint r R τ (j + 1) := by
  have h := iterationPoint_succ_sub r R τ j
  have : 0 < iterationPoint r R τ (j + 1) - iterationPoint r R τ j := by
    rw [h]
    exact mul_pos (sub_pos.2 hrR) (mul_pos (pow_pos hτ0 j) (sub_pos.2 hτ1))
  linarith

/-- The `j`-th step of the iteration: the power `((t_{j+1} - t_j))^{-β}` splits as
`(R - r)^{-β} (1 - τ)^{-β} (τ^{-β})^j`. -/
theorem iterationStep_rpow {r R τ : ℝ} (β : ℝ) (hrR : r < R) (hτ0 : 0 < τ) (hτ1 : τ < 1) (j : ℕ) :
    (iterationPoint r R τ (j + 1) - iterationPoint r R τ j) ^ (-β) =
      (R - r) ^ (-β) * (1 - τ) ^ (-β) * (τ ^ (-β)) ^ j := by
  rw [iterationPoint_succ_sub, Real.mul_rpow (sub_pos.2 hrR).le
    (mul_nonneg (pow_nonneg hτ0.le j) (sub_pos.2 hτ1).le),
    Real.mul_rpow (pow_nonneg hτ0.le j) (sub_pos.2 hτ1).le, ← Real.rpow_natCast τ j,
    ← Real.rpow_mul hτ0.le, mul_comm (j : ℝ) (-β), Real.rpow_mul hτ0.le, Real.rpow_natCast]
  ring

/-- The `N`-step inequality of the iteration lemma. -/
theorem iteration_steps {ψ : ℝ → ℝ} {t₀ t₁ θ A B β τ r R : ℝ} (hθ : 0 ≤ θ) (hτ0 : 0 < τ)
    (hτ1 : τ < 1) (hr : t₀ ≤ r) (hrR : r < R) (hR : R ≤ t₁)
    (h : ∀ t s, t₀ ≤ t → t < s → s ≤ t₁ → ψ t ≤ θ * ψ s + A * (s - t) ^ (-β) + B) (N : ℕ) :
    ψ r ≤ θ ^ N * ψ (iterationPoint r R τ N) +
      ∑ j ∈ range N, θ ^ j * (A * ((R - r) ^ (-β) * (1 - τ) ^ (-β) * (τ ^ (-β)) ^ j) + B) := by
  induction N with
  | zero => simp [iterationPoint_zero]
  | succ N ih =>
    have hN := h (iterationPoint r R τ N) (iterationPoint r R τ (N + 1))
      (hr.trans (iterationPoint_ge hrR.le hτ0.le hτ1.le N))
      (iterationPoint_lt_succ hrR hτ0 hτ1 N)
      ((iterationPoint_lt hrR hτ0 (N + 1)).le.trans hR)
    rw [iterationStep_rpow β hrR hτ0 hτ1 N] at hN
    have hθN : 0 ≤ θ ^ N := pow_nonneg hθ N
    calc ψ r ≤ θ ^ N * ψ (iterationPoint r R τ N) +
          ∑ j ∈ range N, θ ^ j * (A * ((R - r) ^ (-β) * (1 - τ) ^ (-β) * (τ ^ (-β)) ^ j) + B) :=
          ih
      _ ≤ θ ^ N * (θ * ψ (iterationPoint r R τ (N + 1)) +
            A * ((R - r) ^ (-β) * (1 - τ) ^ (-β) * (τ ^ (-β)) ^ N) + B) +
          ∑ j ∈ range N, θ ^ j * (A * ((R - r) ^ (-β) * (1 - τ) ^ (-β) * (τ ^ (-β)) ^ j) + B) :=
          add_le_add (mul_le_mul_of_nonneg_left hN hθN) le_rfl
      _ = θ ^ (N + 1) * ψ (iterationPoint r R τ (N + 1)) +
          ∑ j ∈ range (N + 1),
            θ ^ j * (A * ((R - r) ^ (-β) * (1 - τ) ^ (-β) * (τ ^ (-β)) ^ j) + B) := by
          rw [sum_range_succ, pow_succ]
          ring

theorem geom_sum_le_inv {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    ∑ j ∈ range N, q ^ j ≤ (1 - q)⁻¹ := by
  have h1 : 0 < 1 - q := sub_pos.2 hq1
  have h2 := geom_sum_mul_neg q N
  have hqN : 0 ≤ q ^ N := pow_nonneg hq0 N
  rw [← one_div, le_div_iff₀ h1, h2]
  linarith

/-- The iteration lemma for a fixed ratio `τ ∈ (0, 1)` with `θ τ^{-β} < 1` (BB p. 385, Lem 8.55:
`ψ(r) ≤ θ^N ψ(t_N) + A (1-τ)^{-β}(R-r)^{-β} ∑ (θτ^{-β})^j + B ∑ θ^j`, then `N → ∞`). -/
theorem iteration_core {ψ : ℝ → ℝ} {t₀ t₁ θ A B β τ r R : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hq : θ * τ ^ (-β) < 1)
    (hbdd : ∃ K, ∀ t ∈ Icc t₀ t₁, ψ t ≤ K)
    (h : ∀ t s, t₀ ≤ t → t < s → s ≤ t₁ → ψ t ≤ θ * ψ s + A * (s - t) ^ (-β) + B)
    (hr : t₀ ≤ r) (hrR : r < R) (hR : R ≤ t₁) :
    ψ r ≤ A * ((R - r) ^ (-β) * (1 - τ) ^ (-β)) * (1 - θ * τ ^ (-β))⁻¹ + B * (1 - θ)⁻¹ := by
  obtain ⟨K, hK⟩ := hbdd
  set c : ℝ := (R - r) ^ (-β) * (1 - τ) ^ (-β) with hc
  have hc0 : 0 ≤ c := mul_nonneg (Real.rpow_nonneg (sub_pos.2 hrR).le _)
    (Real.rpow_nonneg (sub_pos.2 hτ1).le _)
  have hq0 : 0 ≤ θ * τ ^ (-β) := mul_nonneg hθ (Real.rpow_nonneg hτ0.le _)
  have key : ∀ N : ℕ, ψ r ≤ θ ^ N * K +
      (A * c * (1 - θ * τ ^ (-β))⁻¹ + B * (1 - θ)⁻¹) := by
    intro N
    have h1 := iteration_steps (β := β) (A := A) (B := B) hθ hτ0 hτ1 hr hrR hR h N
    have hmem : iterationPoint r R τ N ∈ Icc t₀ t₁ :=
      ⟨hr.trans (iterationPoint_ge hrR.le hτ0.le hτ1.le N),
        (iterationPoint_lt hrR hτ0 N).le.trans hR⟩
    have h2 : θ ^ N * ψ (iterationPoint r R τ N) ≤ θ ^ N * K :=
      mul_le_mul_of_nonneg_left (hK _ hmem) (pow_nonneg hθ N)
    have hsum : ∑ j ∈ range N, θ ^ j * (A * ((R - r) ^ (-β) * (1 - τ) ^ (-β) * (τ ^ (-β)) ^ j) + B)
        = A * c * ∑ j ∈ range N, (θ * τ ^ (-β)) ^ j + B * ∑ j ∈ range N, θ ^ j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_pow, hc]
      ring
    have h3 : A * c * ∑ j ∈ range N, (θ * τ ^ (-β)) ^ j ≤ A * c * (1 - θ * τ ^ (-β))⁻¹ :=
      mul_le_mul_of_nonneg_left (geom_sum_le_inv hq0 hq N) (mul_nonneg hA hc0)
    have h4 : B * ∑ j ∈ range N, θ ^ j ≤ B * (1 - θ)⁻¹ :=
      mul_le_mul_of_nonneg_left (geom_sum_le_inv hθ hθ1 N) hB
    rw [hsum] at h1
    linarith
  have hlim : Tendsto (fun N : ℕ => θ ^ N * K +
      (A * c * (1 - θ * τ ^ (-β))⁻¹ + B * (1 - θ)⁻¹)) atTop
      (𝓝 (0 * K + (A * c * (1 - θ * τ ^ (-β))⁻¹ + B * (1 - θ)⁻¹))) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1).mul_const K).add_const _
  have := ge_of_tendsto' hlim key
  rw [zero_mul, zero_add] at this
  exact this

/-- A ratio `τ ∈ (0, 1)` with `θ τ^{-β} < 1`: `τ = ((1 + θ)/2)^{1/β}` for `β > 0` and any fixed
`τ` (here `1/2`) for `β = 0`. -/
theorem exists_iteration_ratio {θ β : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ : 0 ≤ β) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧ θ * τ ^ (-β) < 1 := by
  rcases hβ.eq_or_lt with h0 | hpos
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    rw [← h0, neg_zero, Real.rpow_zero]
    linarith
  · have hm0 : 0 < (1 + θ) / 2 := by linarith
    have hm1 : (1 + θ) / 2 < 1 := by linarith
    refine ⟨((1 + θ) / 2) ^ (1 / β), Real.rpow_pos_of_pos hm0 _,
      Real.rpow_lt_one hm0.le hm1 (by positivity), ?_⟩
    rw [← Real.rpow_mul hm0.le, show 1 / β * -β = -1 by field_simp, Real.rpow_neg_one]
    rw [inv_div, mul_div_assoc', div_lt_one (by linarith)]
    linarith

/-- The case `0 ≤ θ < 1/3`: the constant depends on `β` only
(`τ` is chosen from `β` and the bound `θ < 1/3`; `β = 0` is included with a fixed `τ`). -/
theorem exists_iteration_third {β : ℝ} (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ : ℝ), 0 ≤ θ → θ < 1 / 3 →
      ∀ (ψ : ℝ → ℝ) (t₀ t₁ A B : ℝ), 0 ≤ A → 0 ≤ B →
      (∃ K, ∀ t ∈ Icc t₀ t₁, ψ t ≤ K) →
      (∀ t s, t₀ ≤ t → t < s → s ≤ t₁ → ψ t ≤ θ * ψ s + A * (s - t) ^ (-β) + B) →
      ∀ r R, t₀ ≤ r → r < R → R ≤ t₁ → ψ r ≤ C * (A * (R - r) ^ (-β) + B) := by
  obtain ⟨τ, hτ0, hτ1, hq⟩ := exists_iteration_ratio (θ := 1 / 2) (β := β) (by norm_num)
    (by norm_num) hβ
  have hcA : 0 < (1 - τ) ^ (-β) := Real.rpow_pos_of_pos (sub_pos.2 hτ1) _
  refine ⟨3 * (1 - τ) ^ (-β) + 3 / 2, by positivity, ?_⟩
  intro θ hθ0 hθ3 ψ t₀ t₁ A B hA hB hbdd h r R hr hrR hR
  have hθ1 : θ < 1 := by linarith
  have hτβ : τ ^ (-β) < 2 := by
    have : 1 / 2 * τ ^ (-β) < 1 := hq
    linarith
  have hτβ0 : 0 ≤ τ ^ (-β) := Real.rpow_nonneg hτ0.le _
  have hq' : θ * τ ^ (-β) ≤ 2 / 3 := by nlinarith
  have hq0 : 0 ≤ θ * τ ^ (-β) := mul_nonneg hθ0 hτβ0
  have h1 := iteration_core hθ0 hθ1 hA hB hτ0 hτ1 (by linarith) hbdd h hr hrR hR
  have hinv1 : (1 - θ * τ ^ (-β))⁻¹ ≤ 3 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hinv2 : (1 - θ)⁻¹ ≤ 3 / 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hP : 0 ≤ A * (R - r) ^ (-β) := mul_nonneg hA (Real.rpow_nonneg (sub_pos.2 hrR).le _)
  have hi1 : 0 ≤ (1 - θ * τ ^ (-β))⁻¹ := inv_nonneg.2 (by linarith)
  calc ψ r ≤ A * ((R - r) ^ (-β) * (1 - τ) ^ (-β)) * (1 - θ * τ ^ (-β))⁻¹ + B * (1 - θ)⁻¹ := h1
    _ = (A * (R - r) ^ (-β)) * ((1 - τ) ^ (-β) * (1 - θ * τ ^ (-β))⁻¹) + B * (1 - θ)⁻¹ := by
        ring
    _ ≤ (A * (R - r) ^ (-β)) * ((1 - τ) ^ (-β) * 3) + B * (3 / 2) :=
        add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv1 hcA.le) hP)
          (mul_le_mul_of_nonneg_left hinv2 hB)
    _ ≤ (3 * (1 - τ) ^ (-β) + 3 / 2) * (A * (R - r) ^ (-β) + B) := by
        nlinarith [mul_nonneg hcA.le hB, hP, hB]

end RothschildStein.P2

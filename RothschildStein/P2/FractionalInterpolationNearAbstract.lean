-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RestrictedErrorHolder

/-!
# Hölder interpolation: dyadic Hölder bound for a kernel of bounded support

The abstract dyadic-shell machinery of the restricted-error estimates (`ShellData`, `SliceBounds`) bounds the operator of a
kernel on a set `S` of diameter `< 2ρ` in `L^∞ → C^α` with constant `C ρ^{1-α}`. Here the kernel
vanishes at `dr ≥ r₀` and `S` is large: the Hölder estimate for a pair `(x, x')` at distance `< r₀`
only sees the ball `S ∩ {dr x' · < 3 r₀}`, a `ShellData` of radius `3 r₀`
(`ShellData.restrict_ball`), on which the restricted kernel still has the `SliceBounds`
(`SliceBounds.restrict`). The result is `|T f x - T f x'| ≤ C r₀^{1-α} M dr(x, x')^α` and
`|T f x| ≤ C r₀ M` (`holder_bound_of_support`), the fractional bound with a small constant used for
the near part of BB pp. 594-595, Lem 11.51 (kernel supported at distance `O(h)`, constant
`C h^{1-α}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RothschildStein.P2

open RothschildStein.P1

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {S : Set E} {dr : E → E → ℝ} {q : ℕ}
  {ρ Cv : ℝ}

/-- Restricting the abstract shell data to a ball `S ∩ {dr x' · < R'}` gives shell data of
radius `R'`. -/
theorem shellData_restrict_ball (h : ShellData μ S dr q ρ Cv) {x' : E} (hx' : x' ∈ S) {R' : ℝ}
    (hR' : 0 < R') : ShellData μ (S ∩ {y | dr x' y < R'}) dr q R' Cv where
  measurableSet := h.measurableSet_ball_all hx' R'
  ρ_pos := hR'
  Cv_nonneg := h.Cv_nonneg
  dr_nonneg := fun x hx y hy => h.dr_nonneg x hx.1 y hy.1
  dr_self := fun x hx => h.dr_self x hx.1
  dr_symm := fun x hx y hy => h.dr_symm x hx.1 y hy.1
  dr_tri := fun x hx y hy z hz => h.dr_tri x hx.1 y hy.1 z hz.1
  dr_lt := by
    intro x hx y hy
    have h1 : dr x' x < R' := hx.2
    have h2 : dr x' y < R' := hy.2
    have h3 := h.dr_tri x hx.1 x' hx' y hy.1
    have h4 := h.dr_symm x hx.1 x' hx'
    linarith
  measurableSet_ball := by
    intro x hx t ht _
    have : (S ∩ {y | dr x' y < R'}) ∩ {y | dr x y < t} =
        (S ∩ {y | dr x y < t}) ∩ (S ∩ {y | dr x' y < R'}) := by
      ext y; simp only [mem_inter_iff, mem_ofPred_eq]; tauto
    rw [this]
    exact (h.measurableSet_ball_all hx.1 t).inter (h.measurableSet_ball_all hx' R')
  measure_ball_le := by
    intro x hx t ht _
    have hsub : (S ∩ {y | dr x' y < R'}) ∩ {y | dr x y < t} ⊆ S ∩ {y | dr x y < t} :=
      fun y hy => ⟨hy.1.1, hy.2⟩
    exact (measure_mono hsub).trans (h.measure_ball_le_all hx.1 ht)

/-- The slice bounds survive restriction of the kernel to `S' × S'` for `S' ⊆ S` measurable. -/
theorem sliceBounds_restrict {K : E → E → ℝ} {A B : ℝ} (h : SliceBounds S dr q K A B)
    {S' : Set E} (hS' : S' ⊆ S) (hm : MeasurableSet S') :
    SliceBounds S' dr q ((S' ×ˢ S').indicator (Function.uncurry K) |> Function.curry) A B where
  A_nonneg := h.A_nonneg
  B_nonneg := h.B_nonneg
  measurable := by
    have : Function.uncurry ((S' ×ˢ S').indicator (Function.uncurry K) |> Function.curry) =
        (S' ×ˢ S').indicator (Function.uncurry K) := by
      funext z; rfl
    rw [this]
    exact h.measurable.indicator (hm.prod hm)
  zero_left := fun x y hx => by
    simp [Function.curry, Set.indicator, hx]
  zero_right := fun x y hy => by
    simp [Function.curry, Set.indicator, hy]
  size := fun x hx y hy => by
    simpa [Function.curry, Set.indicator, hx, hy] using h.size x (hS' hx) y (hS' hy)
  diff := fun x hx x' hx' y hy hsep => by
    simpa [Function.curry, Set.indicator, hx, hx', hy] using h.diff x (hS' hx) x' (hS' hx') y
      (hS' hy) hsep

variable {K : E → E → ℝ} {A B : ℝ}

/-- **Sup bound for a kernel of bounded support**: if `K x y = 0` for `dr x y ≥ r₀`, then
`|∫_S K(x, y) f(y) dy| ≤ A M C₁ r₀` with `C₁ = Cv 2^(q+1)`, for `|f| ≤ M`. -/
theorem sup_bound_of_support (hS : ShellData μ S dr q ρ Cv) (hK : SliceBounds S dr q K A B)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hsupp : ∀ x ∈ S, ∀ y ∈ S, r₀ ≤ dr x y → K x y = 0)
    {f : E → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y ∈ S, |f y| ≤ M) {x : E} (hx : x ∈ S) :
    |∫ y in S, K x y * f y ∂μ| ≤ A * M * (Cv * 2 ^ (q + 1)) * r₀ := by
  have hA := hK.A_nonneg
  have hC := hS.Cv_nonneg
  set N : Set E := S ∩ {y | dr x y ≤ r₀} with hN
  have hNm : MeasurableSet N := hS.measurableSet_closedBall hx r₀
  have e : ∫ y in S, K x y * f y ∂μ = ∫ y in N, K x y * f y ∂μ := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS.measurableSet inter_subset_left
      (fun y hy => ?_)
    have : r₀ ≤ dr x y := by
      by_contra hc
      exact hy.2 ⟨hy.1, (not_le.mp hc).le⟩
    rw [hsupp x hx y hy.1 this, zero_mul]
  rw [e]
  have h1 := ofReal_abs_integral_le (fun y => K x y * f y) (μ.restrict N)
  have hnn : 0 ≤ A * M * (Cv * 2 ^ (q + 1)) * r₀ := by positivity
  have h2 : ∫⁻ y in N, ‖K x y * f y‖ₑ ∂μ ≤ ENNReal.ofReal (A * M * (Cv * 2 ^ (q + 1)) * r₀) :=
    (setLIntegral_mono' hNm fun y hy => hK.enorm_mul_le hS hx hy.1 (hM y hy.1)).trans
      (hS.lintegral_ball_le hx (mul_nonneg hA hM0) hr₀.le)
  exact (ENNReal.ofReal_le_ofReal_iff hnn).mp (h1.trans h2)

/-- **Hölder bound for a kernel of bounded support** (the near part of BB pp. 594-595):
if `K x y = 0` for `dr x y ≥ r₀`, then for `0 < α < 1`, `|f| ≤ M` on `S` and `x, x' ∈ S`,
`|T f x - T f x'| ≤ (3 C_α + 2 A C₁) r₀^{1-α} M dr(x, x')^α`, `C₁ = Cv 2^(q+1)`, with the constant
of the restricted-error Hölder bound. -/
theorem holder_bound_of_support (hS : ShellData μ S dr q ρ Cv) (hK : SliceBounds S dr q K A B)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hsupp : ∀ x ∈ S, ∀ y ∈ S, r₀ ≤ dr x y → K x y = 0)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {f : E → ℝ}
    (hf : AEStronglyMeasurable f (μ.restrict S)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ S, |f y| ≤ M) {x x' : E} (hx : x ∈ S) (hx' : x' ∈ S) :
    |∫ y in S, K x y * f y ∂μ - ∫ y in S, K x' y * f y ∂μ| ≤
      (3 * holderConst A B Cv q α + 2 * A * (Cv * 2 ^ (q + 1))) * r₀ ^ (1 - α) * M *
        dr x x' ^ α := by
  have hA := hK.A_nonneg
  have hB := hK.B_nonneg
  have hC := hS.Cv_nonneg
  have hC₁ : 0 ≤ Cv * 2 ^ (q + 1) := by positivity
  have hα' : 0 < 1 - α := by linarith
  have hCα : 0 ≤ holderConst A B Cv q α := by
    unfold holderConst; positivity
  have hδ0 : 0 ≤ dr x x' := hS.dr_nonneg x hx x' hx'
  have hr₀α : 0 < r₀ ^ (1 - α) := Real.rpow_pos_of_pos hr₀ _
  have hδα : 0 ≤ dr x x' ^ α := Real.rpow_nonneg hδ0 _
  by_cases hδ : r₀ ≤ dr x x'
  · -- far pair: both values are small
    have h1 := sup_bound_of_support hS hK hr₀ hsupp hM0 hM hx
    have h2 := sup_bound_of_support hS hK hr₀ hsupp hM0 hM hx'
    have hr₀le : r₀ ≤ r₀ ^ (1 - α) * dr x x' ^ α := by
      calc r₀ = r₀ ^ (1 - α) * r₀ ^ α := by
            rw [← Real.rpow_add hr₀]; simp
        _ ≤ r₀ ^ (1 - α) * dr x x' ^ α :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr₀.le hδ hα0.le) hr₀α.le
    calc _ ≤ |∫ y in S, K x y * f y ∂μ| + |∫ y in S, K x' y * f y ∂μ| := abs_sub _ _
      _ ≤ A * M * (Cv * 2 ^ (q + 1)) * r₀ + A * M * (Cv * 2 ^ (q + 1)) * r₀ := add_le_add h1 h2
      _ = 2 * A * (Cv * 2 ^ (q + 1)) * M * r₀ := by ring
      _ ≤ 2 * A * (Cv * 2 ^ (q + 1)) * M * (r₀ ^ (1 - α) * dr x x' ^ α) :=
          mul_le_mul_of_nonneg_left hr₀le (by positivity)
      _ ≤ (3 * holderConst A B Cv q α + 2 * A * (Cv * 2 ^ (q + 1))) * r₀ ^ (1 - α) * M *
          dr x x' ^ α := by
          have : 0 ≤ r₀ ^ (1 - α) * M * dr x x' ^ α := by positivity
          nlinarith [mul_nonneg hCα this]
  · -- near pair: restrict to the ball of radius `3 r₀` around `x'`
    have hδ' : dr x x' < r₀ := not_le.mp hδ
    set S' : Set E := S ∩ {y | dr x' y < 3 * r₀} with hS'def
    have h3 : 0 < 3 * r₀ := by linarith
    have hS' : ShellData μ S' dr q (3 * r₀) Cv := shellData_restrict_ball hS hx' h3
    have hSS' : S' ⊆ S := inter_subset_left
    have hK' := sliceBounds_restrict hK hSS' hS'.measurableSet
    have hxS' : x ∈ S' := ⟨hx, by
      show dr x' x < 3 * r₀
      rw [hS.dr_symm x' hx' x hx]; linarith⟩
    have hx'S' : x' ∈ S' := ⟨hx', by
      show dr x' x' < 3 * r₀
      rw [hS.dr_self x' hx']; exact h3⟩
    have hf' : AEStronglyMeasurable f (μ.restrict S') :=
      hf.mono_measure (Measure.restrict_mono hSS' le_rfl)
    have hM' : ∀ y ∈ S', |f y| ≤ M := fun y hy => hM y hy.1
    have hhol := hK'.abs_sub_le_holder hS' hf' hM0 hM' hα0 hα1 hxS' hx'S'
    have glue : ∀ z ∈ S', (∀ y ∈ S \ S', K z y = 0) →
        ∫ y in S, K z y * f y ∂μ =
          ∫ y in S', ((S' ×ˢ S').indicator (Function.uncurry K) |> Function.curry) z y * f y ∂μ := by
      intro z hz h0
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS.measurableSet hSS'
        (fun y hy => by rw [h0 y hy, zero_mul])]
      refine setIntegral_congr_fun hS'.measurableSet (fun y hy => ?_)
      simp [Function.curry, Set.indicator, hz, hy]
    have g1 : ∫ y in S, K x y * f y ∂μ =
        ∫ y in S', ((S' ×ˢ S').indicator (Function.uncurry K) |> Function.curry) x y * f y ∂μ := by
      refine glue x hxS' (fun y hy => hsupp x hx y hy.1 ?_)
      have h4 : 3 * r₀ ≤ dr x' y := by
        by_contra hc
        exact hy.2 ⟨hy.1, not_le.mp hc⟩
      have h5 := hS.dr_tri x' hx' x hx y hy.1
      have h6 := hS.dr_symm x' hx' x hx
      linarith
    have g2 : ∫ y in S, K x' y * f y ∂μ =
        ∫ y in S', ((S' ×ˢ S').indicator (Function.uncurry K) |> Function.curry) x' y * f y ∂μ := by
      refine glue x' hx'S' (fun y hy => hsupp x' hx' y hy.1 ?_)
      have h4 : 3 * r₀ ≤ dr x' y := by
        by_contra hc
        exact hy.2 ⟨hy.1, not_le.mp hc⟩
      linarith
    rw [g1, g2]
    refine hhol.trans ?_
    have h3r : (3 * r₀) ^ (1 - α) ≤ 3 * r₀ ^ (1 - α) := by
      rw [Real.mul_rpow (by norm_num) hr₀.le]
      refine mul_le_mul_of_nonneg_right ?_ hr₀α.le
      calc (3 : ℝ) ^ (1 - α) ≤ 3 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 3 := Real.rpow_one 3
    calc holderConst A B Cv q α * (3 * r₀) ^ (1 - α) * M * dr x x' ^ α
        ≤ holderConst A B Cv q α * (3 * r₀ ^ (1 - α)) * M * dr x x' ^ α := by
          gcongr
      _ ≤ (3 * holderConst A B Cv q α + 2 * A * (Cv * 2 ^ (q + 1))) * r₀ ^ (1 - α) * M *
          dr x x' ^ α := by
          have : 0 ≤ r₀ ^ (1 - α) * M * dr x x' ^ α := by positivity
          nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hA (by norm_num : (0 : ℝ) ≤ 2)) hC₁) this]

end RothschildStein.P2

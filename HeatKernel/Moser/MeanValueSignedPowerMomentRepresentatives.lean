-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValuePowerMomentRepresentatives
public import HeatKernel.Moser.MeanValueEnergyIntegrability
import Mathlib.Tactic

/-! # Positive-part moments of signed energy curves -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace HeatKernel

/-- A truncated half-power value energy is bounded by the full extended power
moment, without an upper bound or integrability assumption on that power. -/
theorem positive_half_power_value_energy_le_lintegral_rpow_signed {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {M p : ℝ}
    (hM : 0 < M) (hp : 2 ≤ p) (z : zeroBoundaryGraph V X) :
    ENNReal.ofReal (‖((linearTailPowerWeakSolutionTest hM
      (show 1 ≤ p / 2 by linarith)).energyMap V X hX z :
        GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ≤
      ∫⁻ x, ‖max ((z : GradientSpace (N := N) ⊤ q).fst x) 0‖ₑ ^ p ∂volume := by
  let H := (linearTailPowerWeakSolutionTest hM (show 1 ≤ p / 2 by linarith)).energyMap V X hX z
  have hm : MemLp ((H : GradientSpace (N := N) ⊤ q).fst) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp ((H : GradientSpace (N := N) ⊤ q).fst)
  rw [(Sobolev.gradientSpace_norms_sq_eq_integrals_of_ae_eq
    (H : GradientSpace (N := N) ⊤ q) Filter.EventuallyEq.rfl
      (fun _ => Filter.EventuallyEq.rfl)).1,
    ofReal_integral_eq_lintegral_ofReal hm.integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  apply lintegral_mono_ae
  filter_upwards [(linearTailPowerWeakSolutionTest_energyMap_ae V X hX hM
    (show 1 ≤ p / 2 by linarith) z).1] with x hv
  by_cases hx : 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x
  ·
    rw [hv, max_eq_left hx, Real.enorm_of_nonneg hx, ENNReal.ofReal_rpow_of_nonneg hx (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    have h0 : 0 ≤ linearTailPositivePower M (p / 2) ((z : GradientSpace (N := N) ⊤ q).fst x) := by
      unfold linearTailPositivePower boundedPositivePower
      positivity
    have hb := mul_self_le_mul_self h0 (linearTailPositivePower_le_rpow hM
      (show 1 ≤ p / 2 by linarith) hx)
    have he : (((z : GradientSpace (N := N) ⊤ q).fst x) ^ (p / 2)) ^ 2 =
        (z : GradientSpace (N := N) ⊤ q).fst x ^ p := by
      rw [← Real.rpow_two, ← Real.rpow_mul hx]
      congr 1
      ring
    simpa only [← pow_two, he] using hb
  · rw [hv, linearTailPositivePower_eq_zero_of_nonpos hM
      (show 0 < p / 2 by linarith only [hp]) (lt_of_not_ge hx).le]
    simp only [zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero, zero_le]

/-- A square-integrable graph curve with the stated value representative has a
truncated half-power moment bounded by the full extended power moment. No weak
time equation or integrability of the full power is needed. -/
theorem positive_half_power_value_moment_le_of_signed_representatives
    {μ : Measure ℝ} {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {u : ℝ → (Fin N → ℝ) → ℝ} {φ : (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X} (hv : MemLp v 2 μ)
    (hval : ∀ᵐ t ∂μ, (v t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => u t x * φ x)
    {M p : ℝ} (hM : 0 < M) (hp2 : 2 ≤ p) :
    let H := fun t => (linearTailPowerWeakSolutionTest hM
      (show 1 ≤ p / 2 by linarith only [hp2])).energyMap V X hX (v t)
    ENNReal.ofReal (∫ t, ‖(H t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ∂μ) ≤
      ∫⁻ t, ∫⁻ x, ‖max (u t x * φ x) 0‖ₑ ^ p ∂volume ∂μ := by
  dsimp only
  have hHv := (linearTailPowerWeakSolutionTest hM
    (show 1 ≤ p / 2 by linarith only [hp2])).memLp_energyMap V X hX hv
  have hi := integrable_zeroBoundary_scaled_energy V X μ hHv 0
  simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add] at hi
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun t => sq_nonneg _)]
  apply lintegral_mono_ae
  filter_upwards [hval] with t hvt
  exact (positive_half_power_value_energy_le_lintegral_rpow_signed V X hX hM hp2 (v t)).trans_eq
    (lintegral_congr_ae (hvt.mono fun x hx => by dsimp at hx ⊢; rw [hx]))

/-- A graph moment estimate for the localized truncated half-power becomes the
literal power estimate for its value representative. This is a comparison of
moments and uses no weak time equation. -/
theorem localized_positive_half_power_moment_le_of_signed_graph_moment
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {μ : Measure ℝ} {u : ℝ → (Fin N → ℝ) → ℝ} {η φ : (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X} (hv : MemLp v 2 μ)
    (hval : ∀ᵐ t ∂μ, (v t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => u t x * φ x)
    (hW : W.toFun =ᵐ[volume] η) (hplateau : ∀ x, η x ≠ 0 → φ x = 1)
    {M p ν A C : ℝ} (hM : 0 < M) (hp2 : 2 ≤ p) (hν : 0 < ν) (θ : ℝ → ℝ) :
    let H := fun t => (linearTailPowerWeakSolutionTest hM
      (show 1 ≤ p / 2 by linarith only [hp2])).energyMap V X hX (v t)
    let w := fun t => θ t • W.multiplier (H t)
    ((∫⁻ t, ∫⁻ x, ‖(w t : GradientSpace (N := N) ⊤ q).fst x‖ₑ ^
      (2 + 4 / ν) ∂volume ∂μ) ≤
        ENNReal.ofReal A * (ENNReal.ofReal C * ENNReal.ofReal
          (∫ t, ‖(H t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ∂μ)) ^ (1 + 2 / ν)) →
    (∫⁻ t, ∫⁻ x, ‖θ t * η x * linearTailPositivePower M (p / 2) (u t x)‖ₑ ^
      (2 + 4 / ν) ∂volume ∂μ) ≤
        ENNReal.ofReal A *
          (ENNReal.ofReal C * (∫⁻ t, ∫⁻ x, ‖max (u t x * φ x) 0‖ₑ ^ p ∂volume ∂μ)) ^
            (1 + 2 / ν) := by
  dsimp only
  intro hbound
  let H := fun t => (linearTailPowerWeakSolutionTest hM
    (show 1 ≤ p / 2 by linarith only [hp2])).energyMap V X hX (v t)
  let w := fun t => θ t • W.multiplier (H t)
  have hm := positive_half_power_value_moment_le_of_signed_representatives V X hX hv hval hM hp2
  have hrep : ∀ᵐ t ∂μ,
      (w t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        fun x => θ t * η x * linearTailPositivePower M (p / 2) (u t x) := by
    filter_upwards [hval] with t ht
    exact W.localized_linearTail_half_power_value_ae hX hW hplateau hM hp2 (v t) ht (θ t)
  have heq :
      (∫⁻ t, ∫⁻ x, ‖(w t : GradientSpace (N := N) ⊤ q).fst x‖ₑ ^
        (2 + 4 / ν) ∂volume ∂μ) =
      ∫⁻ t, ∫⁻ x, ‖θ t * η x * linearTailPositivePower M (p / 2) (u t x)‖ₑ ^
        (2 + 4 / ν) ∂volume ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hrep] with t ht
    exact lintegral_congr_ae (ht.mono fun x hx => by dsimp at hx ⊢; rw [hx])
  rw [heq] at hbound
  exact hbound.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow
    (mul_le_mul' le_rfl hm) (by positivity)))


end HeatKernel

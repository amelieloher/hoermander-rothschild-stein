-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSignedMatrixEnergyBudget
public import HeatKernel.Moser.MeanValuePowerEnergyRepresentatives
public import HeatKernel.Moser.MeanValueTerminalMomentBudget
import Mathlib.Tactic

/-! # Elliptic matrix energy budgets bounded by a truncated value moment -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- The actual elliptic matrix power test gives uniform terminal and total
gradient budgets in terms of its truncated half-power value moment, uniformly
in the truncation height and without an upper bound on the nonnegative value.
No spatial flux absorption or terminal energy estimate is assumed. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.signed_matrix_positive_power_budget_le_value_moment
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B a b Htime L M p ell upper : ℝ}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    (hell : 0 ≤ ell) (hupper : 0 ≤ upper)
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X
      coeff (Icc A B) u g φ k v F)
    (hcoeff_meas : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∀ i j, AEStronglyMeasurable (fun x => coeff t x i j) volume)
    (hcoeff_sym : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∀ᵐ x ∂volume, ∀ i j, coeff t x i j = coeff t x j i)
    (hcoeff_elliptic : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∀ᵐ x ∂volume, ∀ ξ : Fin q → ℝ,
        ell * coordinateNormSq ξ ≤ matrixEnergy (coeff t x) ξ ∧
        matrixEnergy (coeff t x) ξ ≤ upper * coordinateNormSq ξ)
    (W : WeakSolutionSpatialWeight V X)
    {η : (Fin N → ℝ) → ℝ} {d : Fin q → (Fin N → ℝ) → ℝ}
    (hη : AEStronglyMeasurable η volume) (hηb : ∀ᵐ x ∂volume, ‖η x‖ ≤ 1)
    (hL : 0 ≤ L) (hd : ∀ᵐ x ∂volume, (∑ i, d i x ^ 2) ≤ L)
    (hW : ∀ᵐ x ∂volume, W.toFun x = η x ^ 2)
    (hWd : ∀ i, ∀ᵐ x ∂volume, W.gradient i x = 2 * η x * d i x)
    (hplateau : ∀ x, W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, k i x = 0)
    (hM : 0 < M) (hp2 : 2 ≤ p)
    (hab : a < b) (hAa : A < a) (hbB : b < B)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (hχa : χ a = 0)
    (hχunit : ∀ t ∈ Icc a b, χ t ∈ Icc (0 : ℝ) 1)
    (hHtime : 0 ≤ Htime) (hχderiv : ∀ t ∈ Icc a b, deriv χ t ≤ Htime) :
    let H := fun t => (linearTailPowerWeakSolutionTest hM
      (show 1 ≤ p / 2 by linarith)).energyMap V X hX (v t)
    let T := linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)
    let D := fun t => (ell / p) * coefficientEnergy ⊤ X
      (fun i j x => η x ^ 2 * if i = j then 1 else 0)
      (zeroBoundaryEnergyInclusion V X (H t)) (zeroBoundaryEnergyInclusion V X (H t))
    IntegrableOn D (Icc a b) ∧
    (∀ᵐ s ∂volume.restrict (Icc a b),
      χ s * W.energy T (v s) + (∫ t in Icc a s, χ t * D t) ≤
        (Htime / 2 + 2 * upper * L) *
          (∫ t in Icc a b, ‖(H t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2)) ∧
      (∫ t in Icc a b, χ t * D t) ≤
        (Htime / 2 + 2 * upper * L) *
          (∫ t in Icc a b, ‖(H t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) := by
  dsimp only
  let H := fun t => (linearTailPowerWeakSolutionTest hM
    (show 1 ≤ p / 2 by linarith)).energyMap V X hX (v t)
  let T := linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)
  obtain ⟨hDi, hbudget⟩ := hp.ae_signed_matrix_positive_power_energy_budget hX hell hupper
    hcoeff_meas hcoeff_sym hcoeff_elliptic W hη hηb hd hW hWd
    hplateau hM hp2 hab.le hAa hbB hχ hχa (fun t ht => (hχunit t ht).1)
  have hWunit : ∀ᵐ x ∂volume, W.toFun x ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [hW, hηb] with x hx hb
    rw [hx]
    have ha : -1 ≤ η x ∧ η x ≤ 1 := abs_le.mp (by simpa only [Real.norm_eq_abs] using hb)
    exact ⟨sq_nonneg _, by nlinarith [ha.1, ha.2]⟩
  have hEb : ∀ᵐ t ∂volume.restrict (Icc a b),
      0 ≤ W.energy T (v t) ∧ W.energy T (v t) ≤
        ‖(H t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 / 2 :=
    Filter.Eventually.of_forall fun t => W.positive_power_energy_bounds_of_signed_value hX hWunit hM hp2 (v t)
  have hHv := (linearTailPowerWeakSolutionTest hM
    (show 1 ≤ p / 2 by linarith)).memLp_energyMap V X hX hp.1
  have hmAB : IntegrableOn (fun t => ‖(H t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2)
      (Icc A B) := by
    simpa only [IntegrableOn, H, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add] using
      integrable_zeroBoundary_scaled_energy V X (volume.restrict (Icc A B)) hHv 0
  have hsub : Icc a b ⊆ Icc A B := fun t ht =>
    ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  refine ⟨hDi, ?_⟩
  have hb := terminal_energy_budget_le_full_value_moment (L := upper * L) hab
    (by norm_num : (0 : ℝ) < 2) hHtime (mul_nonneg hupper hL)
    (hp.integrableOn_spatial_energy hX W T hab.le hAa hbB) hDi (hmAB.mono_set hsub)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hEb.mono fun _ ht => ht.1)
    (hEb.mono fun _ ht => ht.2) hχ hχunit hχderiv (by simpa only [mul_assoc] using hbudget)
  simpa only [mul_assoc] using hb

end HeatKernel

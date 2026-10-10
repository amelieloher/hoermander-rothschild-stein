-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSignedPowerScalars
public import HeatKernel.Moser.WeakSolutionAffineIntegrals
public import HeatKernel.Sobolev.GradientRepresentativeMoments
import Mathlib.Tactic

/-! # Power energies and localized half-power slice norms -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- A nonnegative unit spatial weight gives a nonnegative positive-part primitive
energy, bounded by half the half-power value energy. The graph value may have either sign. -/
theorem WeakSolutionSpatialWeight.positive_power_energy_bounds_of_signed_value {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hW : ∀ᵐ x ∂volume, W.toFun x ∈ Icc (0 : ℝ) 1)
    {M p : ℝ} (hM : 0 < M) (hp : 2 ≤ p) (z : zeroBoundaryGraph V X) :
    0 ≤ W.energy (linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)) z ∧
      W.energy (linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)) z ≤
        ‖((linearTailPowerWeakSolutionTest hM (show 1 ≤ p / 2 by linarith)).energyMap
          V X hX z : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 / 2 := by
  let T := linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)
  let H := (linearTailPowerWeakSolutionTest hM (show 1 ≤ p / 2 by linarith)).energyMap V X hX z
  have hv := (linearTailPowerWeakSolutionTest_energyMap_ae V X hX hM
    (show 1 ≤ p / 2 by linarith) z).1
  have hm : MemLp ((H : GradientSpace (N := N) ⊤ q).fst) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp ((H : GradientSpace (N := N) ⊤ q).fst)
  have hprim0 : ∀ᵐ x ∂volume, 0 ≤ T.primitive ((z : GradientSpace (N := N) ⊤ q).fst x) := by
    filter_upwards [] with x
    have h := linearTailPositivePower_half_sq_le_primitive_signed (s := (z : GradientSpace (N := N) ⊤ q).fst x) hM hp
    dsimp only [T]
    nlinarith [sq_nonneg (linearTailPositivePower M (p / 2)
      ((z : GradientSpace (N := N) ⊤ q).fst x))]
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [hW, hprim0] with x hw hx
    exact mul_nonneg hw.1 hx
  · have hb := integral_mono_ae (W.integrable_energy_density T z)
      (hm.integrable_sq.div_const 2) (by
        filter_upwards [hW, hprim0, hv] with x hw hx hvx
        change W.toFun x * T.primitive _ ≤ (H : GradientSpace (N := N) ⊤ q).fst x ^ 2 / 2
        rw [hvx]
        exact ((mul_le_mul_of_nonneg_right hw.2 hx).trans_eq (one_mul _)).trans
          (linearTailPowerWeakSolutionTest_primitive_le_half_sq_signed hM hp))
    rw [integral_div, ← (Sobolev.gradientSpace_norms_sq_eq_integrals_of_ae_eq
      (H : GradientSpace (N := N) ⊤ q) Filter.EventuallyEq.rfl
        (fun _ => Filter.EventuallyEq.rfl)).1] at hb
    exact hb

/-- The square-cutoff primitive controls the actual localized half-power slice
norm, uniformly on both truncation regions. No full power integrability is required. -/
theorem WeakSolutionSpatialWeight.cutoff_positive_half_power_slice_le_primitive {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W S : WeakSolutionSpatialWeight V X)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {η : (Fin N → ℝ) → ℝ}
    (hW : W.toFun =ᵐ[volume] η) (hS : S.toFun =ᵐ[volume] fun x => η x ^ 2)
    {M p : ℝ} (hM : 0 < M) (hp : 2 ≤ p) (z : zeroBoundaryGraph V X) :
    ‖(W.multiplier ((linearTailPowerWeakSolutionTest hM
      (show 1 ≤ p / 2 by linarith)).energyMap V X hX z) :
        GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤
      p * S.energy (linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)) z := by
  let H := (linearTailPowerWeakSolutionTest hM (show 1 ≤ p / 2 by linarith)).energyMap V X hX z
  let T := linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)
  let y := W.multiplier H
  have hy : MemLp ((y : GradientSpace (N := N) ⊤ q).fst) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp ((y : GradientSpace (N := N) ⊤ q).fst)
  have hv := (linearTailPowerWeakSolutionTest_energyMap_ae V X hX hM
    (show 1 ≤ p / 2 by linarith) z).1
  have hb := integral_mono_ae hy.integrable_sq ((S.integrable_energy_density T z).const_mul p) (by
    filter_upwards [W.value_ae H, hv, hW, hS] with x hx hvx hw hs
    dsimp only [y, H]
    rw [hx, hw, hvx, hs, mul_pow]
    have he := mul_le_mul_of_nonneg_left
      (linearTailPositivePower_half_sq_le_primitive_signed (s := (z : GradientSpace (N := N) ⊤ q).fst x) hM hp) (sq_nonneg (η x))
    dsimp only [T]
    convert he using 1
    ring)
  rw [integral_const_mul, ← (Sobolev.gradientSpace_norms_sq_eq_integrals_of_ae_eq
    (y : GradientSpace (N := N) ⊤ q) Filter.EventuallyEq.rfl
      (fun _ => Filter.EventuallyEq.rfl)).1] at hb
  exact hb

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.CaccioppoliMatrixSpatialAbsorption
public import HeatKernel.Moser.MeanValueSignedPowerScalars
public import HeatKernel.Moser.MeanValueHalfPowerEnergy
public import HeatKernel.Moser.CaccioppoliSpatialPowerTest
public import HeatKernel.Moser.WeakSolutionSpatialTransport
import Mathlib.Tactic

/-! # Positive-part elliptic matrix flux for signed energy values -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- The square-cutoff matrix flux controls the truncated half-power gradient.
The value may have either sign. Bounded measurable coefficients and the energy graph supply integrability. -/
theorem WeakSolutionSpatialWeight.positive_power_flux_absorption_of_signed_value {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {η : (Fin N → ℝ) → ℝ} {d : Fin q → (Fin N → ℝ) → ℝ} {K L M p ell upper : ℝ}
    (a : Fin q → Fin q → (Fin N → ℝ) → ℝ)
    (hell : 0 ≤ ell) (hupper : 0 ≤ upper)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) volume)
    (hsym : ∀ᵐ x ∂volume, ∀ i j, a i j x = a j i x)
    (helliptic : ∀ᵐ x ∂volume, ∀ ξ : Fin q → ℝ,
      ell * coordinateNormSq ξ ≤ matrixEnergy (fun i j => a i j x) ξ ∧
      matrixEnergy (fun i j => a i j x) ξ ≤ upper * coordinateNormSq ξ)
    (hη : AEStronglyMeasurable η volume) (hηb : ∀ᵐ x ∂volume, ‖η x‖ ≤ K)
    (hd : ∀ᵐ x ∂volume, (∑ i, d i x ^ 2) ≤ L)
    (hW : ∀ᵐ x ∂volume, W.toFun x = η x ^ 2)
    (hWd : ∀ i, ∀ᵐ x ∂volume, W.gradient i x = 2 * η x * d i x)
    (hM : 0 < M) (hp : 2 ≤ p) (z : zeroBoundaryGraph V X) :
    (ell / p) * (∫ x, ∑ i, (η x *
      ((linearTailPowerWeakSolutionTest hM (show 1 ≤ p / 2 by linarith)).energyMap
        V X hX z : GradientSpace (N := N) ⊤ q).snd i x) ^ 2) ≤
      coefficientEnergy ⊤ X a
        (zeroBoundaryEnergyInclusion V X z)
        (zeroBoundaryEnergyInclusion V X
          (W.energyMap hX (linearTailPowerWeakSolutionTest hM
            (show 1 ≤ p - 1 by linarith)) z)) +
      2 * upper * L * (∫ x,
        ((linearTailPowerWeakSolutionTest hM (show 1 ≤ p / 2 by linarith)).energyMap
          V X hX z : GradientSpace (N := N) ⊤ q).fst x ^ 2) := by
  let H := (linearTailPowerWeakSolutionTest hM (show 1 ≤ p / 2 by linarith)).energyMap V X hX z
  let T := linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)
  let Z := W.energyMap hX T z
  have hH := linearTailPowerWeakSolutionTest_energyMap_ae V X hX hM
    (show 1 ≤ p / 2 by linarith) z
  have hZ := caccioppoli_spatial_power_test_gradient_ae W hX η d hW hWd hM hp z
  have hgrad (i : Fin q) : MemLp ((H : GradientSpace (N := N) ⊤ q).snd i) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp ((H : GradientSpace (N := N) ⊤ q).snd i)
  have hval : MemLp ((H : GradientSpace (N := N) ⊤ q).fst) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp ((H : GradientSpace (N := N) ⊤ q).fst)
  have hD : Integrable (fun x => ∑ i,
      (η x * (H : GradientSpace (N := N) ⊤ q).snd i x) ^ 2) volume :=
    integrable_finsetSum _ (fun i _ =>
      (memLp_two_mul_of_ae_bound hη (hgrad i) hηb).integrable_sq)
  have hb (i j : Fin q) : ∀ᵐ x ∂volume, ‖a i j x‖ ≤ upper := by
    filter_upwards [hsym, helliptic] with x hs he
    exact norm_matrix_entry_le_of_elliptic_bounds (fun i j => a i j x) hell hs he i j
  have hF : Integrable (coefficientEnergyDensity ⊤ X a
      (zeroBoundaryEnergyInclusion V X z) (zeroBoundaryEnergyInclusion V X Z)) volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      integrable_coefficientEnergyDensity ⊤ X a
        (zeroBoundaryEnergyInclusion V X z) (zeroBoundaryEnergyInclusion V X Z)
        (by simpa only [Opens.coe_top, Measure.restrict_univ] using ha)
        (by simpa only [Opens.coe_top, Measure.restrict_univ] using hb)
  have hbound := integral_mono_ae (hD.const_mul (ell / p))
    (hF.add (hval.integrable_sq.const_mul (2 * upper * L))) (by
      filter_upwards [hd, hH.1, ae_all_iff.mpr hH.2, ae_all_iff.mpr hZ,
        hsym, helliptic] with x hdx hv hg htest hs he
      by_cases hx : 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x
      ·
        have hpos (ξ : Fin q → ℝ) : 0 ≤ matrixEnergy (fun i j => a i j x) ξ :=
          (mul_nonneg hell (Finset.sum_nonneg fun i _ => sq_nonneg (ξ i))).trans (he ξ).1
        have habs := caccioppoli_matrix_half_power_flux (fun i j => a i j x) hs hpos
          hM hp hx (η x) (fun i => (z : GradientSpace (N := N) ⊤ q).snd i x)
          (fun i => d i x) (he _).1 (he _).2
        have hcut := caccioppoli_power_cutoff_error_le_half_sq hM hp hx
        have herr := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcut
            (show 0 ≤ coordinateNormSq (fun i => d i x) from
              Finset.sum_nonneg fun i _ => sq_nonneg (d i x))) hupper
        have herror := mul_le_mul_of_nonneg_left hdx
          (show 0 ≤ 2 * upper * linearTailPositivePower M (p / 2)
            ((z : GradientSpace (N := N) ⊤ q).fst x) ^ 2 by positivity)
        have heq : coefficientEnergyDensity ⊤ X a
            (zeroBoundaryEnergyInclusion V X z) (zeroBoundaryEnergyInclusion V X Z) x =
            linearTailPositivePowerSlope M (p - 1)
              ((z : GradientSpace (N := N) ⊤ q).fst x) * η x ^ 2 *
                matrixEnergy (fun i j => a i j x)
                  (fun i => (z : GradientSpace (N := N) ⊤ q).snd i x) +
            2 * T.toFun ((z : GradientSpace (N := N) ⊤ q).fst x) * η x *
              (∑ i, ∑ j, a i j x * (z : GradientSpace (N := N) ⊤ q).snd j x * d i x) := by
          change (∑ i, ∑ j, a i j x * (z : GradientSpace (N := N) ⊤ q).snd j x *
            (Z : GradientSpace (N := N) ⊤ q).snd i x) = _
          dsimp only [Z, T]
          simp only [htest, matrixEnergy, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          simp only [linearTailPowerWeakSolutionTest]
          ring
        have hgrad_eq : (∑ i, (η x *
            (linearTailPositivePowerSlope M (p / 2)
              ((z : GradientSpace (N := N) ⊤ q).fst x) *
                (z : GradientSpace (N := N) ⊤ q).snd i x)) ^ 2) =
            linearTailPositivePowerSlope M (p / 2)
              ((z : GradientSpace (N := N) ⊤ q).fst x) ^ 2 * η x ^ 2 *
                coordinateNormSq (fun i => (z : GradientSpace (N := N) ⊤ q).snd i x) := by
          simp only [coordinateNormSq, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        dsimp only [H]
        simp only [Pi.add_apply, hg, hv, heq, hgrad_eq]
        dsimp only [T]
        simp only [coordinateNormSq] at habs herr ⊢
        nlinarith only [habs, herr, herror]
      · have hn : (z : GradientSpace (N := N) ⊤ q).fst x ≤ 0 := (lt_of_not_ge hx).le
        have hz := linearTailPositivePower_eq_zero_of_nonpos hM
          (show 0 < p / 2 by linarith only [hp]) hn
        have ht := linearTailPositivePower_eq_zero_of_nonpos hM
          (show 0 < p - 1 by linarith only [hp]) hn
        have hsl (γ : ℝ) : linearTailPositivePowerSlope M γ
            ((z : GradientSpace (N := N) ⊤ q).fst x) = 0 := by
          simp only [linearTailPositivePowerSlope, not_lt.mpr hn, ite_false]
        have htest0 (i : Fin q) : (Z : GradientSpace (N := N) ⊤ q).snd i x = 0 := by
          simpa only [Z, T, linearTailPowerWeakSolutionTest, hsl, ht, mul_zero,
            zero_mul, add_zero] using htest i
        change (ell / p) * (∑ i, (η x * (H : GradientSpace (N := N) ⊤ q).snd i x) ^ 2) ≤ _
        simp only [H, hg, hv, hsl, hz, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0),
          Finset.sum_const_zero, Pi.add_apply]
        change 0 ≤ coefficientEnergyDensity ⊤ X a
          (zeroBoundaryEnergyInclusion V X z) (zeroBoundaryEnergyInclusion V X Z) x + 0
        change 0 ≤ (∑ i, ∑ j, a i j x *
          (z : GradientSpace (N := N) ⊤ q).snd j x *
          (Z : GradientSpace (N := N) ⊤ q).snd i x) + 0
        simp only [htest0, mul_zero, Finset.sum_const_zero, add_zero, le_refl])

  have hsum := integral_add hF (hval.integrable_sq.const_mul (2 * upper * L))
  simp only [Pi.add_apply] at hbound
  rw [hsum, integral_const_mul, integral_const_mul] at hbound
  simpa only [coefficientEnergy, Opens.coe_top, Measure.restrict_univ] using hbound

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSignedMatrixFlux
public import HeatKernel.Moser.MeanValueIdentityEnergyBudget

/-! # Positive-part terminal energy for signed matrix weak solutions -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Elliptic matrix weak solutions satisfy a terminal truncated-power energy
budget. The spatial flux estimate and all energy integrability are conclusions
of the weak cutoff pair and the square-cutoff gradient bound. The plateau conditions
specify only the relation between the two spatial localization cutoffs. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.ae_signed_matrix_positive_power_energy_budget
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B a b K L M p ell upper : ℝ}
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
    (hη : AEStronglyMeasurable η volume) (hηb : ∀ᵐ x ∂volume, ‖η x‖ ≤ K)
    (hd : ∀ᵐ x ∂volume, (∑ i, d i x ^ 2) ≤ L)
    (hW : ∀ᵐ x ∂volume, W.toFun x = η x ^ 2)
    (hWd : ∀ i, ∀ᵐ x ∂volume, W.gradient i x = 2 * η x * d i x)
    (hplateau : ∀ x, W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, k i x = 0)
    (hM : 0 < M) (hp2 : 2 ≤ p)
    (hab : a ≤ b) (hAa : A < a) (hbB : b < B)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (hχa : χ a = 0)
    (hχ0 : ∀ t ∈ Icc a b, 0 ≤ χ t) :
    let H := fun t => (linearTailPowerWeakSolutionTest hM
      (show 1 ≤ p / 2 by linarith)).energyMap V X hX (v t)
    let T := linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)
    let D := fun t => (ell / p) * coefficientEnergy ⊤ X
      (fun i j x => η x ^ 2 * if i = j then 1 else 0)
      (zeroBoundaryEnergyInclusion V X (H t)) (zeroBoundaryEnergyInclusion V X (H t))
    IntegrableOn D (Icc a b) ∧
      ∀ᵐ s ∂volume.restrict (Icc a b),
        χ s * W.energy T (v s) + (∫ t in Icc a s, χ t * D t) ≤
          ∫ t in Icc a s, deriv χ t * W.energy T (v t) +
            χ t * (2 * upper * L * ‖(H t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) := by
  dsimp only
  let H := fun t => (linearTailPowerWeakSolutionTest hM
    (show 1 ≤ p / 2 by linarith)).energyMap V X hX (v t)
  let T := linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)
  let D := fun t => (ell / p) * coefficientEnergy ⊤ X
    (fun i j x => η x ^ 2 * if i = j then 1 else 0)
    (zeroBoundaryEnergyInclusion V X (H t)) (zeroBoundaryEnergyInclusion V X (H t))
  have hsub : Icc a b ⊆ Icc A B := fun t ht =>
    ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  have hHv := (linearTailPowerWeakSolutionTest hM
    (show 1 ≤ p / 2 by linarith)).memLp_energyMap V X hX hp.1
  have hHi := (zeroBoundaryEnergyInclusion V X).comp_memLp' hHv
  have hcoeff := integrable_coefficientEnergy_curves ⊤ X
    (μ := volume.restrict (Icc A B))
    (fun i j z => η z.2 ^ 2 * if i = j then 1 else 0) (sq_nonneg K)
    (fun i j => by
      simpa only [Opens.coe_top, Measure.restrict_univ, Pi.mul_def, Pi.pow_def] using
        (hη.comp_snd.pow 2).mul aestronglyMeasurable_const)
    (fun i j => by
      simp only [Opens.coe_top, Measure.restrict_univ]
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae hηb] with z hz
      by_cases hij : i = j
      · simpa only [hij, ite_true, mul_one, norm_pow] using
          pow_le_pow_left₀ (norm_nonneg (η z.2)) hz 2
      · simp only [hij, ite_false, mul_zero, norm_zero]
        exact sq_nonneg K)
    _ _ hHi hHi
  have hDiAB : IntegrableOn D (Icc A B) := hcoeff.const_mul (ell / p)
  have hDi : IntegrableOn D (Icc a b) := hDiAB.mono_set hsub
  have hR : IntegrableOn
      (fun t => 2 * upper * L * ‖(H t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) (Icc a b) := by
    have hi := integrable_zeroBoundary_scaled_energy V X (volume.restrict (Icc A B)) hHv 0
    simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add] at hi
    have hiAB : IntegrableOn
        (fun t => 2 * upper * L * ‖(H t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) (Icc A B) :=
      hi.const_mul (2 * upper * L)
    exact hiAB.mono_set hsub
  apply hp.ae_terminal_spatial_energy_budget hX W T hab hAa hbB hχ hχa hχ0
    hDi.aestronglyMeasurable ?_ hR ?_
  · exact Filter.Eventually.of_forall fun t => by
      dsimp only [D]
      rw [square_weighted_identity_coefficientEnergy_eq_integral]
      exact mul_nonneg (by positivity) (integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)
  · have hgrad := (ae_all_iff.mpr hp.2.2.2.1).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hflux := hp.2.2.2.2.2.1.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    filter_upwards [hgrad, hflux, hcoeff_meas, hcoeff_sym, hcoeff_elliptic]
      with t hgt hft hmt hst het
    have hbt (i j : Fin q) : ∀ᵐ x ∂volume, ‖coeff t x i j‖ ≤ upper := by
      filter_upwards [hst, het] with x hs he
      exact norm_matrix_entry_le_of_elliptic_bounds (coeff t x) hell hs he i j
    have hF := W.flux_eq_coefficientEnergy_of_plateau hX T
      (fun i j x => coeff t x i j) (C := upper) hmt hbt
      (v t) (F t) hgt hft hplateau
    have hb := W.positive_power_flux_absorption_of_signed_value hX (fun i j x => coeff t x i j)
      hell hupper hmt hst het hη hηb hd hW hWd hM hp2 (v t)
    have hv := (Sobolev.gradientSpace_norms_sq_eq_integrals_of_ae_eq
      (H t : GradientSpace (N := N) ⊤ q) Filter.EventuallyEq.rfl
      (fun _ => Filter.EventuallyEq.rfl)).1
    dsimp only [D]
    rw [square_weighted_identity_coefficientEnergy_eq_integral, hF, hv]
    exact hb

end HeatKernel

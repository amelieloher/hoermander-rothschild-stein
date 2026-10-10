-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueMatrixCutoffPair
public import HeatKernel.Moser.MeanValueSmoothSpatialWeights
public import HeatKernel.Moser.MeanValueMatrixSobolevEnergy
public import HeatKernel.Moser.MeanValueSobolevEnergyMoments
public import HeatKernel.Moser.MeanValueSignedPowerMomentRepresentatives
import Mathlib.Tactic

/-! # Positive-part power moments of signed matrix weak solutions -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Signed uniformly elliptic matrix weak solutions satisfy the localized
truncated positive-power moment estimate, uniformly in the truncation height.
Smooth nested spatial cutoffs and a lower-time cutoff are the geometric inputs. The energy curve,
nonlinear time identity, spatial flux absorption and Sobolev energy estimates
are all supplied by the weak equation. -/
theorem exists_uniform_signed_matrix_positive_power_moment_constant {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (I : Opens ℝ) (U V : Opens (Fin N → ℝ)),
      volume (V : Set (Fin N → ℝ)) ≠ ⊤ →
      ∀ u : ℝ → (Fin N → ℝ) → ℝ,
      ∀ coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ,
      IsLocalWeakSolution G hq hqpos hw hspan coeff I U u →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      ∀ A₀ B a b : ℝ, Icc A₀ B ⊆ (I : Set ℝ) → a < b → A₀ < a → b < B →
      ∀ φ η : (Fin N → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → (∀ x, φ x ∈ Icc (0 : ℝ) 1) →
      HasCompactSupport φ → tsupport φ ⊆ (U : Set (Fin N → ℝ)) →
      tsupport φ ⊆ (V : Set (Fin N → ℝ)) →
      ContDiff ℝ (⊤ : ℕ∞) η → (∀ x, η x ∈ Icc (0 : ℝ) 1) →
      HasCompactSupport η → tsupport η ⊆ (V : Set (Fin N → ℝ)) →
      (∀ x ∈ tsupport η, φ x = 1 ∧
        ∀ i, fieldDerivative (G.horizontalFields hq i) φ x = 0) →
      ∀ L : ℝ, 0 ≤ L →
      (∀ x, (∑ i, fieldDerivative (G.horizontalFields hq i) η x ^ 2) ≤ L) →
      ∀ θ : ℝ → ℝ, ContDiff ℝ 1 θ → θ a = 0 →
      (∀ t ∈ Icc a b, θ t ∈ Icc (0 : ℝ) 1) →
      ∀ Ttime : ℝ, 0 ≤ Ttime → (∀ t ∈ Icc a b, deriv θ t ≤ Ttime) →
      ∀ p : ℝ, 2 ≤ p → ∀ M : ℝ, 0 < M →
      (∫⁻ t in Icc a b, ∫⁻ x, ‖θ t * η x * linearTailPositivePower M (p / 2) (u t x)‖ₑ ^
        (2 + 4 / ν) ∂volume) ≤
          ENNReal.ofReal A *
            (ENNReal.ofReal (2 * max p (p / ell) * Ttime +
              (4 * max p (p / ell) + 2) * max L (upper * L) + 1) *
              (∫⁻ t in Icc a b, ∫⁻ x, ‖max (u t x * φ x) 0‖ₑ ^ p ∂volume)) ^ (1 + 2 / ν) := by
  obtain ⟨A, hA, hSob⟩ :=
    exists_uniform_parabolic_moment_constant_of_energy_bounds G hq hqpos hspan hw hν
  refine ⟨A, hA, ?_⟩
  intro I U V hfinite u coeff hu ha hbound A₀ B a b hJI hab hAa hbB φ η hφ hφunit hcφ hφU hφV
    hη hηunit hcη hηV hplateau L hL hd θ hθ hθa hθunit Ttime hTtime hθd p hp2 M hM
  have hX := G.horizontalFields_contDiff hq
  obtain ⟨g, v, F, _, hp⟩ := hu.exists_signed_smooth_cutoff_energy_pair
    G hq hqpos hw hspan coeff I U V ha hell.le hbound hJI
      hφ hφunit hcφ hφU hφV
  have hsub : Icc a b ⊆ Icc A₀ B := fun t ht =>
    ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  have hcoeff_meas : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∀ i j, AEStronglyMeasurable (fun x => coeff t x i j) volume :=
    Filter.Eventually.of_forall fun t i j =>
      ((ha i j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hcoeff_slices := (Measure.ae_ae_of_ae_prod hbound).filter_mono
    (ae_mono (Measure.restrict_le_self : volume.restrict (Icc a b) ≤ volume))
  have hcoeff_sym := hcoeff_slices.mono fun t ht => ht.mono fun x hx => hx.1
  have hcoeff_elliptic : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∀ᵐ x ∂volume, ∀ ξ : Fin q → ℝ,
        ell * coordinateNormSq ξ ≤ matrixEnergy (coeff t x) ξ ∧
        matrixEnergy (coeff t x) ξ ≤ upper * coordinateNormSq ξ := by
    filter_upwards [hcoeff_slices] with t ht
    filter_upwards [ht] with x hx ξ
    simpa only [matrixEnergy, coordinateNormSq, mul_assoc, mul_left_comm, mul_comm]
      using hx.2 ξ
  let W := WeakSolutionSpatialWeight.ofSmoothUnitCutoff V (G.horizontalFields hq)
    hX hη hcη hηV hηunit
  obtain ⟨S, hS, hSd⟩ := exists_smooth_square_spatial_weight V (G.horizontalFields hq)
    hX hη hcη hηV hηunit
  have hSp : ∀ x, S.toFun x ≠ 0 ∨ (∃ i, S.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, fieldDerivative (G.horizontalFields hq i) φ x = 0 := by
    intro x hx
    apply hplateau x
    apply subset_tsupport η
    apply Function.mem_support.mpr
    intro hzero
    rcases hx with hx | ⟨i, hi⟩
    · exact hx (by rw [hS, hzero, zero_pow (by decide : 2 ≠ 0)])
    · exact hi (by rw [hSd, hzero, mul_zero, zero_mul])
  have hηb : ∀ᵐ x ∂volume, ‖η x‖ ≤ 1 := Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hηunit x).1] using (hηunit x).2
  obtain ⟨hwm, hslice, henergy⟩ := hp.signed_matrix_positive_power_sobolev_energy_bounds hX hell hupper
    hcoeff_meas hcoeff_sym hcoeff_elliptic W S
    hη.continuous.aestronglyMeasurable hηb hL (Filter.Eventually.of_forall hd)
    Filter.EventuallyEq.rfl (fun _ => Filter.EventuallyEq.rfl)
    (Filter.Eventually.of_forall hS) (fun i => Filter.Eventually.of_forall (hSd i))
    hSp hM hp2 hab hAa hbB
    hθ hθa hθunit hTtime hθd
  let H := fun t => (linearTailPowerWeakSolutionTest hM
    (show 1 ≤ p / 2 by linarith)).energyMap V (G.horizontalFields hq) hX (v t)
  let w := fun t => θ t • W.multiplier (H t)
  have hbound := hSob V hfinite (volume.restrict (Icc a b)) w hwm
    (2 * max p (p / ell) * Ttime +
      (4 * max p (p / ell) + 2) * max L (upper * L) + 1)
    (∫ t in Icc a b, ‖(H t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2)
    (by positivity) (integral_nonneg fun t => sq_nonneg _) hslice henergy
  have hv := hp.2.2.1.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  exact localized_positive_half_power_moment_le_of_signed_graph_moment W hX
    (hp.1.mono_measure (Measure.restrict_mono hsub le_rfl)) hv Filter.EventuallyEq.rfl
    (fun x hx => (hplateau x (subset_tsupport η (Function.mem_support.mpr hx))).1)
    hM hp2 (by have hν0 := lt_of_le_of_lt (le_max_left _ _) hν; linarith only [hν0]) θ hbound

end HeatKernel

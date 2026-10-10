-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderSpatialFluxBound
public import HeatKernel.Moser.ReverseHolderEnergyBudget
public import HeatKernel.Moser.ReverseHolderMoment
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Backward small-positive-power budgets with explicit spatial localization data. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- The original weak time equation and coefficient ellipticity give backward
small-positive-power budgets at all lower endpoints on a localization plateau. Spatial square integrability,
the square-cutoff identities, an integrable spatial weight, measurability of the
diffusion integral, and integrability of the cutoff error are explicit inputs.
The cutoff-gradient bound and its localization plateau are explicit inputs.
Weighted cutoff square integrability follows from the localized energy-space value.
Diffusion integrability and the absorption bound are conclusions.
The time representative equals the literal weighted small-positive-power moment. -/
theorem exists_reverse_holder_initial_energy_budgets_of_plateau
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ η : (Fin N → ℝ) → ℝ} {k d : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B a b c C K Kd ell upper p : ℝ}
    (hpair : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (W : WeakSolutionSpatialWeight V X) (hc : 0 < c) (hell : 0 < ell) (hp : 0 < p) (hp2 : p ≤ 1 / 2)
    (w : zeroBoundaryGraph V X) (hWint : Integrable W.toFun volume)
    (hab : a ≤ b) (hAa : A < a) (hbB : b < B)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (hdw : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i)
    (hplateau : ∀ x, W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, k i x = 0)
    (hW : ∀ x, W.toFun x = η x ^ 2) (hWd : ∀ i x, W.gradient i x = 2 * η x * d i x)
    (hη : AEStronglyMeasurable η volume) (hηbound : ∀ᵐ x ∂volume, ‖η x‖ ≤ K)
    (hd : ∀ i, MemLp (d i) 2 volume)
    (hdbound : ∀ i, ∀ᵐ x ∂volume, ‖d i x‖ ≤ Kd)
    (hdplateau : ∀ i x, d i x ≠ 0 → φ x = 1)
    (hdata : ∀ᵐ t ∂volume.restrict (Icc a b),
      (∀ᵐ x ∂volume, 0 ≤ (v t : GradientSpace (N := N) ⊤ q).fst x) ∧
      AEStronglyMeasurable (u t) volume ∧ (∀ᵐ x ∂volume, 0 ≤ u t x) ∧
      (∀ i j, AEStronglyMeasurable (fun x => coeff t x i j) volume) ∧
      (∀ i j, ∀ᵐ x ∂volume, ‖coeff t x i j‖ ≤ C) ∧
      (∀ i, MemLp (g i t) 2 volume) ∧
      (∀ᵐ x ∂volume, (∀ i j, coeff t x i j = coeff t x j i) ∧ ∀ ξ : Fin q → ℝ,
        ell * coordinateNormSq ξ ≤ matrixEnergy (coeff t x) ξ ∧
        matrixEnergy (coeff t x) ξ ≤ upper * coordinateNormSq ξ))
    (hDmeas : AEStronglyMeasurable
      (fun t => ∫ x, 2 * ell * (p / 2) ^ 2 * coordinateNormSq
        (fun i => η x * ((u t x + c) ^ (p / 2 - 1) * g i t x)))
      (volume.restrict (Icc a b)))
    (hR : IntegrableOn (fun t => ∫ x, 2 * upper * (u t x + c) ^ p *
      coordinateNormSq (fun i => d i x)) (Icc a b))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (hχb : χ b = 0)
    (hχpos : ∀ᵐ t ∂volume, 0 ≤ χ t) :
    let D := fun t => ∫ x, 2 * ell * (p / 2) ^ 2 * coordinateNormSq
      (fun i => η x * ((u t x + c) ^ (p / 2 - 1) * g i t x))
    let R := fun t => ∫ x, 2 * upper * (u t x + c) ^ p * coordinateNormSq (fun i => d i x)
    IntegrableOn D (Icc a b) ∧ ∃ e : ℝ → ℝ, AbsolutelyContinuousOnInterval e a b ∧
      e =ᵐ[volume.restrict (Icc a b)]
        (fun t => ∫ x, η x ^ 2 * (u t x + c) ^ p) ∧
      ∀ s ∈ Icc a b, χ s * e s + (∫ t in s..b, χ t * D t) ≤
        (∫ t in s..b, -(deriv χ t) * e t) + ∫ t in s..b, χ t * R t := by
  dsimp only
  let T := shiftedRpowWeakSolutionTest hc (p := p - 1) (by linarith)
  let D := fun t => ∫ x, 2 * ell * (p / 2) ^ 2 * coordinateNormSq
    (fun i => η x * ((u t x + c) ^ (p / 2 - 1) * g i t x))
  let R := fun t => ∫ x, 2 * upper * (u t x + c) ^ p * coordinateNormSq (fun i => d i x)
  have hsub : Icc a b ⊆ Icc A B := fun t ht => ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  have hle := ae_mono (Measure.restrict_mono hsub (le_refl volume))
  have hgrad := (ae_all_iff.mpr hpair.2.2.2.1).filter_mono hle
  have hval := hpair.2.2.1.filter_mono hle
  have hflux := hpair.2.2.2.2.2.1.filter_mono hle
  have hcut : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ i,
      MemLp (fun x => (u t x + c) ^ (p / 2) * d i x) 2 volume := by
    filter_upwards [hval, hdata] with t hvt hdt
    intro i
    have hv : MemLp (v t : GradientSpace (N := N) ⊤ q).fst 2 volume := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        Lp.memLp (v t : GradientSpace (N := N) ⊤ q).fst
    exact memLp_shifted_small_power_mul_of_plateau hc (by positivity : 0 ≤ p / 2)
      (by linarith : p / 2 ≤ 1) hv hdt.1 (hd i) (hdbound i) hvt (hdplateau i)
  have habs : ∀ᵐ t ∂volume.restrict (Icc a b),
      D t ≤ -p * F t (W.affineEnergyMap hX T w (c ^ (p - 1)) (v t)) + R t := by
    filter_upwards [hdata, hgrad, hval, hflux, hcut] with t ht hgt hvt hft hct
    obtain ⟨hz, hu, hupos, ha, hb, hg, hcoeff⟩ := ht
    exact (W.reverse_holder_flux_bound_of_plateau (fun i j x => coeff t x i j)
      hX hc hell hp hp2 (v t) w (F t) hz hw hdw hvt hgt hft hplateau hW hWd
      hu hupos hη hηbound ha hb hg hd hct hcoeff).2.2
  have hD0 (t : ℝ) : 0 ≤ D t := by
    apply integral_nonneg
    intro x
    have hn : 0 ≤ coordinateNormSq
        (fun i => η x * ((u t x + c) ^ (p / 2 - 1) * g i t x)) := by
      unfold coordinateNormSq
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    exact mul_nonneg (by positivity) hn
  have hf := ((hpair.integrable_affine_energy_flux hX W T w (c ^ (p - 1))).mono_set
    hsub).const_mul (-p)
  have hD : IntegrableOn D (Icc a b) := (hf.add hR).mono' hDmeas (by
    filter_upwards [habs] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hD0 t), Pi.add_apply] using ht)
  obtain ⟨e, he, heq, hbudget⟩ := exists_reverse_holder_initial_energy_budgets_of_flux_bound
    hpair hX W hc (by linarith : p ≤ 1) w (c ^ p * ∫ x, W.toFun x)
      hab hAa hbB D R hD hR habs hχ hχb hχpos
  refine ⟨hD, e, he, ?_, hbudget⟩
  filter_upwards [heq, hdata, hval] with t ht hdt hvt
  rw [ht, reverse_holder_corrected_energy_eq_moment_of_plateau W hc hp (by linarith : p ≤ 1) hWint w hw
    (v t) hdt.1 hvt (fun x hx => (hplateau x (Or.inl hx)).1)]
  simp only [hW]

end HeatKernel

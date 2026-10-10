-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicCorrectedMeanRepresentative
public import HeatKernel.Moser.LogarithmicTentCutoffEnergy
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Corrected logarithmic means with the exact distance-tent error constant -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
namespace HeatKernel

/-- The literal squared distance tent supplies the uniform correction constant in
the actual weak-solution logarithmic mean estimate. No normalized cutoff-energy
inequality is assumed. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.exists_corrected_logarithmic_tent_mean
    {N q : ℕ} {V : TopologicalSpace.Opens (Fin N → ℝ)}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hweight : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r upper : ℝ} (hr : 0 < r) (hupper : 0 ≤ upper)
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ η : (Fin N → ℝ) → ℝ} {k d : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V (G.horizontalFields hq)}
    {F : ℝ → (zeroBoundaryGraph V (G.horizontalFields hq) →L[ℝ] ℝ)} {A B a b c C : ℝ}
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V (G.horizontalFields hq) coeff (Icc A B) u g φ k v F)
    (W : WeakSolutionSpatialWeight V (G.horizontalFields hq)) (w : zeroBoundaryGraph V (G.horizontalFields hq))
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (hdw : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i)
    (hplateau : ∀ x, W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, k i x = 0)
    (hz : ∀ᵐ t ∂volume.restrict (Icc A B), ∀ᵐ x ∂volume,
      0 ≤ (v t : GradientSpace (N := N) ⊤ q).fst x)
    (hηtent : η = fun y => max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0)
    (hgrad : ∀ᵐ y ∂volume, y ∈ horizontalBall (G.horizontalFields hq) x r →
      coordinateNormSq (fun i => d i y) ≤ (r ^ 2)⁻¹)
    (hsupport : ∀ᵐ y ∂volume, y ∉ horizontalBall (G.horizontalFields hq) x r →
      ∀ i, d i y = 0)
    (hW : W.toFun =ᵐ[volume] fun x => η x ^ 2)
    (hD : ∀ i, W.gradient i =ᵐ[volume] fun x => 2 * η x * d i x)
    (hd : ∀ i, MemLp (d i) 2 volume)
    (hcoeff : ∀ᵐ t ∂volume.restrict (Icc A B),
      (∀ i j, AEStronglyMeasurable (fun x => coeff t x i j) volume) ∧
      (∀ i j, ∀ᵐ x ∂volume, ‖coeff t x i j‖ ≤ C) ∧
      (∀ᵐ x ∂volume, ∀ i j, coeff t x i j = coeff t x j i) ∧
      (∀ᵐ x ∂volume, ∀ ξ, 0 ≤ matrixEnergy (fun i j => coeff t x i j) ξ))
    (hquad : ∀ᵐ t ∂volume.restrict (Icc A B), ∀ᵐ y ∂volume, ∀ ξ,
      matrixEnergy (fun i j => coeff t y i j) ξ ≤ upper * coordinateNormSq ξ)
    (hc : 0 < c) (hab : a ≤ b) (hAa : A < a) (hbB : b < B) :
    let D := upper * (((G.homogeneousDimension : ℝ) + 1) *
      ((G.homogeneousDimension : ℝ) + 2)) / r ^ 2
    let E := fun t => (∫ x, W.toFun x)⁻¹ * ∫ x, ∑ i, ∑ j, coeff t x i j *
      (η x * ((u t x + c)⁻¹ * g j t x)) *
      (η x * ((u t x + c)⁻¹ * g i t x))
    ∃ e : ℝ → ℝ, AbsolutelyContinuousOnInterval e a b ∧
      e =ᵐ[volume.restrict (Icc a b)]
        (fun t => (∫ x, W.toFun x)⁻¹ *
          ∫ x, W.toFun x * (Real.log (u t x + c) - Real.log c)) ∧
      AbsolutelyContinuousOnInterval (fun t => e t + D * t) a b ∧
      MonotoneOn (fun t => e t + D * t) (Icc a b) ∧
      ∀ᵐ t ∂volume.restrict (Icc a b), E t ≤ 2 * deriv (fun s => e s + D * s) t := by
  have hmassEq : (∫ y, W.toFun y) = ∫ y, η y ^ 2 := integral_congr_ae hW
  have hmass : 0 < ∫ y, W.toFun y := by
    rw [hmassEq, hηtent]
    exact Sobolev.integral_horizontal_tent_sq_pos G hq hqpos hspan hweight x hr
  have hη : AEStronglyMeasurable η volume := by
    rw [hηtent]
    exact ((measurable_const.sub (Sobolev.measurable_horizontalDistance_div G hq hqpos hspan x r)).max
      measurable_const).aestronglyMeasurable
  have hηbound : ∀ᵐ y ∂volume, ‖η y‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro y
    rw [hηtent, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    apply max_le _ (by norm_num)
    have := div_nonneg (ENNReal.toReal_nonneg (a := horizontalL2Distance (G.horizontalFields hq) x y)) hr.le
    linarith
  have hcutoff : ∀ᵐ t ∂volume.restrict (Icc A B),
      2 * (∫ y, W.toFun y)⁻¹ * (∫ y, ∑ i, ∑ j, coeff t y i j * d j y * d i y) ≤
        upper * (((G.homogeneousDimension : ℝ) + 1) *
          ((G.homogeneousDimension : ℝ) + 2)) / r ^ 2 := by
    filter_upwards [hcoeff, hquad] with t ht hqf
    rw [hmassEq, hηtent]
    exact normalized_logarithmic_tent_cutoff_energy_le G hq hqpos hspan hweight x hr
      ht.1 ht.2.1 hd hupper hqf hgrad hsupport
  obtain ⟨e, hac, heq, hcorr, hmono, henergy⟩ :=
    hp.exists_corrected_logarithmic_mean_of_cutoff_energy_bound
    (G.horizontalFields_contDiff hq) W w hw hdw hplateau hz hη hηbound hW hD hd hcoeff
    hcutoff hmass hc hab hAa hbB
  refine ⟨e, hac, heq, hcorr, hmono, ?_⟩
  have hsub : Icc a b ⊆ Icc A B := fun t ht =>
    ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  have hgradtime := ae_all_iff.mpr (fun i =>
    ae_restrict_of_ae_restrict_of_subset hsub (hp.2.2.2.1 i))
  filter_upwards [henergy, ae_restrict_of_ae_restrict_of_subset hsub hp.2.2.1,
    hgradtime] with t he hv hg
  have henergyEq :
      (∫ y, ∑ i, ∑ j, coeff t y i j * (η y * ((u t y + c)⁻¹ * g j t y)) *
        (η y * ((u t y + c)⁻¹ * g i t y))) =
      ∫ y, ∑ i, ∑ j, coeff t y i j *
        (η y * (((v t : GradientSpace (N := N) ⊤ q).fst y + c)⁻¹ *
          (v t : GradientSpace (N := N) ⊤ q).snd j y)) *
        (η y * (((v t : GradientSpace (N := N) ⊤ q).fst y + c)⁻¹ *
          (v t : GradientSpace (N := N) ⊤ q).snd i y)) := by
    apply integral_congr_ae
    filter_upwards [hv, ae_all_iff.mpr hg, hW] with y hy hgy hwy
    by_cases hηzero : η y = 0
    · simp only [hηzero, zero_mul, mul_zero, Finset.sum_const_zero]
    · have hWne : W.toFun y ≠ 0 := by
        rw [hwy]
        exact pow_ne_zero 2 hηzero
      obtain ⟨hφ, hk⟩ := hplateau y (Or.inl hWne)
      have hval : (v t : GradientSpace (N := N) ⊤ q).fst y = u t y := by
        simpa only [hφ, mul_one] using hy
      have hvec (i : Fin q) : (v t : GradientSpace (N := N) ⊤ q).snd i y = g i t y := by
        simpa only [hφ, hk, mul_one, mul_zero, add_zero] using hgy i
      simp only [hval, hvec]
  rw [← henergyEq] at he
  exact he

end HeatKernel

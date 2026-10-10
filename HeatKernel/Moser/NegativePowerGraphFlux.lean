-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerSpatialFluxBound
public import HeatKernel.Moser.TopExhaustionGraphEnergy

/-! # Reciprocal-power absorption using the localized energy graph -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- The centered shifted power has the ordinary weak chain rule, including
zero levels of a nonnegative energy value. -/
theorem shifted_rpow_graph_gradient_ae {N q : ℕ}
    {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {c r : ℝ} (hc : 0 < c) (hr : r ≤ 1)
    (z : zeroBoundaryGraph V X)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x) (i : Fin q) :
    ((shiftedRpowWeakSolutionTest hc hr).energyMap V X hX z :
      GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] fun x =>
      r * ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (r - 1) *
        (z : GradientSpace (N := N) ⊤ q).snd i x := by
  filter_upwards [(shiftedRpowWeakSolutionTest hc hr).energyMap_gradient_ae V X hX z i,
    hz, energyGraph_gradient_zero_on_level X hX (zeroBoundaryEnergyInclusion V X z) 0 i]
    with x hx hn hzero
  rw [hx]
  by_cases hs : 0 < (z : GradientSpace (N := N) ⊤ q).fst x
  · rw [(hasDerivAt_shifted_rpow_test hc hr hs).deriv]
  · have he : (z : GradientSpace (N := N) ⊤ q).fst x = 0 :=
      le_antisymm (le_of_not_gt hs) hn
    have hg : (z : GradientSpace (N := N) ⊤ q).snd i x = 0 := hzero he
    rw [hg, mul_zero, mul_zero]

/-- A Bochner L² cutoff graph supplies time integrability of the reciprocal
diffusion integral. No measurability of the nonlinear diffusion is assumed. -/
theorem integrable_negative_half_power_graph_diffusion {N q : ℕ}
    {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {c p ell K : ℝ} (hc : 0 < c) (hp : 0 < p)
    {η : (Fin N → ℝ) → ℝ} (hη : AEStronglyMeasurable η volume)
    (hηb : ∀ᵐ x ∂volume, ‖η x‖ ≤ K)
    {μ : Measure ℝ} {v : ℝ → zeroBoundaryGraph V X} (hv : MemLp v 2 μ)
    (hz : ∀ᵐ t ∂μ, ∀ᵐ x ∂volume,
      0 ≤ (v t : GradientSpace (N := N) ⊤ q).fst x) :
    Integrable (fun t => ∫ x, 2 * ell * (p / 2) ^ 2 * coordinateNormSq
      (fun i => η x * (((v t : GradientSpace (N := N) ⊤ q).fst x + c) ^
        (-p / 2 - 1) * (v t : GradientSpace (N := N) ⊤ q).snd i x))) μ := by
  let T := shiftedRpowWeakSolutionTest hc (p := -p / 2) (by linarith)
  have hH := T.memLp_energyMap V X hX hv
  have hi := (integrable_weighted_graph_gradient_curve hη hηb hH).const_mul (2 * ell)
  apply hi.congr
  filter_upwards [hz] with t ht
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun i => shifted_rpow_graph_gradient_ae hX
    hc (by linarith : -p / 2 ≤ 1) (v t) ht i)] with x hx
  simp only [T, hx, coordinateNormSq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The localized graph supplies all spatial integrability for reciprocal-power
absorption. The original solution and gradient need only agree with this graph
on the localization plateau. -/
theorem WeakSolutionSpatialWeight.negative_power_graph_flux_bound {N q : ℕ}
    {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (a : Fin q → Fin q → (Fin N → ℝ) → ℝ)
    {u φ η : (Fin N → ℝ) → ℝ} {g k d : Fin q → (Fin N → ℝ) → ℝ}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {c C K ell upper p : ℝ} (hc : 0 < c) (hell : 0 < ell) (hp : 0 < p)
    (z w : zeroBoundaryGraph V X) (F : zeroBoundaryGraph V X →L[ℝ] ℝ)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (hdw : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i)
    (hgrad : ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => g i x * φ x + u x * k i x)
    (hflux : ∀ v, F v = ∑ i, ∫ x, (∑ j, a i j x * g j x) *
      (φ x * (v : GradientSpace (N := N) ⊤ q).snd i x +
        k i x * (v : GradientSpace (N := N) ⊤ q).fst x))
    (hplateau : ∀ x, W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, k i x = 0)
    (hW : ∀ x, W.toFun x = η x ^ 2)
    (hWd : ∀ i x, W.gradient i x = 2 * η x * d i x)
    (hη : AEStronglyMeasurable η volume) (hηbound : ∀ᵐ x ∂volume, ‖η x‖ ≤ K)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) volume)
    (hb : ∀ i j, ∀ᵐ x ∂volume, ‖a i j x‖ ≤ C)
    (hd : ∀ i, MemLp (d i) 2 volume)
    (hcoeff : ∀ᵐ x ∂volume, (∀ i j, a i j x = a j i x) ∧ ∀ ξ : Fin q → ℝ,
      ell * coordinateNormSq ξ ≤ matrixEnergy (fun i j => a i j x) ξ ∧
      matrixEnergy (fun i j => a i j x) ξ ≤ upper * coordinateNormSq ξ) :
    let s := fun x => (z : GradientSpace (N := N) ⊤ q).fst x + c
    let D := fun x => 2 * ell * (p / 2) ^ 2 * coordinateNormSq
      (fun i => η x * (s x ^ (-p / 2 - 1) *
        (z : GradientSpace (N := N) ⊤ q).snd i x))
    let R := fun x => 2 * upper * s x ^ (-p) * coordinateNormSq (fun i => d i x)
    Integrable D volume ∧ Integrable R volume ∧
      (∫ x, D x) ≤ -p * F (W.affineEnergyMap hX
        (shiftedRpowWeakSolutionTest hc (p := -p - 1) (by linarith))
          w (c ^ (-p - 1)) z) + ∫ x, R x := by
  dsimp only
  let v := (z : GradientSpace (N := N) ⊤ q).fst
  let h := fun i => (z : GradientSpace (N := N) ⊤ q).snd i
  have hv : MemLp v 2 volume := by
    simpa only [v, Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp (z : GradientSpace (N := N) ⊤ q).fst
  have hh (i : Fin q) : MemLp (h i) 2 volume := by
    simpa only [h, Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp ((z : GradientSpace (N := N) ⊤ q).snd i)
  obtain ⟨hD, _, hR, hbound⟩ := integrable_negative_power_physical_flux_and_bound
    hc hell hp hv.aestronglyMeasurable hz hη hηbound ha hb hh hd hcoeff
  have hi := integrable_negative_power_coordinate_flux hc hp
    hv.aestronglyMeasurable hz hη hηbound ha hb hh hd
  have heq : F (W.affineEnergyMap hX
      (shiftedRpowWeakSolutionTest hc (p := -p - 1) (by linarith))
        w (c ^ (-p - 1)) z) = ∫ x, ∑ i, (∑ j, a i j x * h j x) *
      (η x ^ 2 * (-p - 1) * (v x + c) ^ (-p - 2) * h i x +
        (2 * η x * d i x) * (v x + c) ^ (-p - 1)) := by
    rw [hflux, integral_finsetSum _ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hgrad,
      negative_power_affine_test_value_ae W hX hc hp w hw z hz,
      W.negative_power_affine_gradient_ae hX hc hp z w hz hdw i]
      with x hg hval hderiv
    rw [hval, hderiv]
    by_cases hactive : W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0)
    · obtain ⟨hφ, hk⟩ := hplateau x hactive
      have he (j : Fin q) : h j x = g j x := by
        simpa only [h, hφ, hk, mul_one, mul_zero, add_zero] using hg j
      simp only [hφ, hk, one_mul, zero_mul, add_zero, hW, hWd, v, h, he]
      congr 1
      ring
    · have hw0 : W.toFun x = 0 := not_ne_iff.mp (fun hn => hactive (Or.inl hn))
      have hd0 : W.gradient i x = 0 :=
        not_ne_iff.mp (fun hn => hactive (Or.inr ⟨i, hn⟩))
      have hη0 : η x = 0 := sq_eq_zero_iff.mp ((hW x).symm.trans hw0)
      simp only [hw0, hd0, hη0, zero_mul, mul_zero, add_zero,
        zero_pow (by decide : 2 ≠ 0)]
  exact ⟨hD, hR, by rw [heq]; exact hbound⟩

end HeatKernel

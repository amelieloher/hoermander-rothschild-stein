-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicReciprocalLocalization
public import HeatKernel.Moser.WeakSolutionSpatialTransport
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Original coefficient flux of a localized reciprocal test -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- On a localization plateau, the reciprocal flux can be written using the
zero-boundary value and gradient. These representatives are globally square
integrable even when the original weak solution is only locally so. -/
theorem WeakSolutionSpatialWeight.reciprocal_affine_flux_eq_localized {N q : ℕ}
    {V : TopologicalSpace.Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (a : Fin q → Fin q → (Fin N → ℝ) → ℝ)
    {u φ : (Fin N → ℝ) → ℝ} {g k : Fin q → (Fin N → ℝ) → ℝ}
    (z w : zeroBoundaryGraph V X) (F : zeroBoundaryGraph V X →L[ℝ] ℝ) {c : ℝ}
    (hc : 0 < c)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (hdw : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i)
    (hgrad : ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => g i x * φ x + u x * k i x)
    (hflux : ∀ v, F v = ∑ i, ∫ x, (∑ j, a i j x * g j x) *
      (φ x * (v : GradientSpace (N := N) ⊤ q).snd i x +
        k i x * (v : GradientSpace (N := N) ⊤ q).fst x))
    (hplateau : ∀ x, W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, k i x = 0) :
    F (W.affineEnergyMap hX (shiftedRpowWeakSolutionTest hc (p := -1) (by norm_num)) w c⁻¹ z) =
      ∑ i, ∫ x, (∑ j, a i j x * (z : GradientSpace (N := N) ⊤ q).snd j x) *
        (W.toFun x * (-(((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ 2)⁻¹ *
          (z : GradientSpace (N := N) ⊤ q).snd i x) +
          W.gradient i x * ((z : GradientSpace (N := N) ⊤ q).fst x + c)⁻¹) := by
  obtain ⟨r, heq, hrval, hrgrad⟩ := W.exists_reciprocal_test hX hc z w hz hw hdw
  rw [← heq, hflux]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr hgrad, hrval, hrgrad i] with x hg hrv hrg
  rw [hrv, hrg]
  by_cases hactive : W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0)
  · obtain ⟨hφ, hk⟩ := hplateau x hactive
    have hzg (j : Fin q) : (z : GradientSpace (N := N) ⊤ q).snd j x = g j x := by
      simpa only [hφ, hk, mul_one, mul_zero, add_zero] using hg j
    simp only [hφ, hk, one_mul, zero_mul, add_zero, hzg]
  · have hW : W.toFun x = 0 := not_ne_iff.mp (fun hn => hactive (Or.inl hn))
    have hD : W.gradient i x = 0 := not_ne_iff.mp (fun hn => hactive (Or.inr ⟨i, hn⟩))
    simp only [hW, hD, zero_mul, mul_zero, add_zero]

end HeatKernel

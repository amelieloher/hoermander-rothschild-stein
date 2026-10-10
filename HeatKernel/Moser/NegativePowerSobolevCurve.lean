-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerShiftedGradient
public import HeatKernel.Moser.MeanValueSpatialSobolev
public import HeatKernel.Moser.MeanValueSobolevMoments
public import HeatKernel.Sobolev.HorizontalSobolevVolume
public import HeatKernel.Sobolev.GradientRepresentativeMoments
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Reciprocal half-power cutoff curves and their uniform parabolic Sobolev bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- The affine-corrected shifted-power curve represents the original localized
solution on a plateau, with both terms of its horizontal product gradient. -/
theorem WeakSolutionSpatialWeight.shifted_rpow_affine_representatives_of_plateau {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {u φ : (Fin N → ℝ) → ℝ} {g k : Fin q → (Fin N → ℝ) → ℝ}
    {c r : ℝ} (hc : 0 < c) (hr : r ≤ 1) (z w : zeroBoundaryGraph V X)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (hdw : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i)
    (hval : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] fun x => u x * φ x)
    (hgrad : ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => g i x * φ x + u x * k i x)
    (hplateau : ∀ x, W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, k i x = 0) :
    let Z := W.affineEnergyMap hX (shiftedRpowWeakSolutionTest hc hr) w (c ^ r) z
    (Z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      (fun x => W.toFun x * (u x + c) ^ r) ∧
    ∀ i, (Z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => W.toFun x * ((r * (u x + c) ^ (r - 1)) * g i x) +
        W.gradient i x * (u x + c) ^ r := by
  dsimp only
  constructor
  · filter_upwards [W.affineEnergyMap_value_ae hX (shiftedRpowWeakSolutionTest hc hr)
      w (c ^ r) hw z, hz, hval] with x hx hpos hvalx
    rw [hx]
    have ht : (shiftedRpowWeakSolutionTest hc hr).toFun
        ((z : GradientSpace (N := N) ⊤ q).fst x) =
        ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ r - c ^ r :=
      Sobolev.zeroPreservingShiftedRpow_eq (c := c) (p := r) hpos
    rw [ht, sub_add_cancel]
    by_cases hactive : W.toFun x = 0
    · simp only [hactive, zero_mul]
    · rw [hvalx, (hplateau x (Or.inl hactive)).1, mul_one]
  · intro i
    filter_upwards [W.shifted_rpow_affine_gradient_ae hX hc hr z w hz hdw i,
      hval, hgrad i] with x hx hv hg
    rw [hx]
    by_cases hactive : W.toFun x ≠ 0 ∨ (∃ j, W.gradient j x ≠ 0)
    · obtain ⟨hφ, hk⟩ := hplateau x hactive
      have hv' : (z : GradientSpace (N := N) ⊤ q).fst x = u x := by
        simpa only [hφ, mul_one] using hv
      have hg' : (z : GradientSpace (N := N) ⊤ q).snd i x = g i x := by
        simpa only [hφ, hk, mul_one, mul_zero, add_zero] using hg
      rw [hv', hg']
    · have hW : W.toFun x = 0 := not_ne_iff.mp (fun hn => hactive (Or.inl hn))
      have hd : W.gradient i x = 0 := not_ne_iff.mp (fun hn => hactive (Or.inr ⟨i, hn⟩))
      simp only [hW, hd, zero_mul, add_zero]

end HeatKernel

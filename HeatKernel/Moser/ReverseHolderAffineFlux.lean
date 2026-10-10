-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderAffineEnergy
public import HeatKernel.Moser.NegativePowerShiftedGradient
public import HeatKernel.Moser.WeakSolutionSpatialTransport
import all Mathlib.Basic.Real.Basic

/-! Original coefficient flux of affine-corrected concave-power tests. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- A localization plateau identifies the restored concave-power test flux with the
original local value and gradient. Both concave-power diffusion and the weight-gradient
flux are retained, without separate integrability assumptions on their summands. -/
theorem WeakSolutionSpatialWeight.reverse_holder_test_flux_eq_of_plateau {N q : ℕ}
    {V : TopologicalSpace.Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (a : Fin q → Fin q → (Fin N → ℝ) → ℝ)
    {u φ : (Fin N → ℝ) → ℝ} {g k : Fin q → (Fin N → ℝ) → ℝ}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {c p : ℝ} (hc : 0 < c) (hp1 : p ≤ 1)
    (z w : zeroBoundaryGraph V X) (F : zeroBoundaryGraph V X →L[ℝ] ℝ)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (hdw : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i)
    (hval : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] fun x => u x * φ x)
    (hgrad : ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => g i x * φ x + u x * k i x)
    (hflux : ∀ v, F v = ∑ i, ∫ x, (∑ j, a i j x * g j x) *
      (φ x * (v : GradientSpace (N := N) ⊤ q).snd i x +
        k i x * (v : GradientSpace (N := N) ⊤ q).fst x))
    (hplateau : ∀ x, W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, k i x = 0) :
    F (W.affineEnergyMap hX (shiftedRpowWeakSolutionTest hc (p := p - 1) (by linarith))
      w (c ^ (p - 1)) z) = ∑ i, ∫ x, (∑ j, a i j x * g j x) *
      (W.toFun x * (((p - 1) * (u x + c) ^ (p - 2)) * g i x) +
        W.gradient i x * (u x + c) ^ (p - 1)) := by
  let T := shiftedRpowWeakSolutionTest hc (p := p - 1) (by linarith)
  have hrval : (W.affineEnergyMap hX T w (c ^ (p - 1)) z :
      GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => W.toFun x * ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (p - 1) := by
    filter_upwards [W.affineEnergyMap_value_ae hX T w _ hw z, hz] with x hx hpos
    rw [hx]
    have ht : T.toFun ((z : GradientSpace (N := N) ⊤ q).fst x) =
        ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (p - 1) - c ^ (p - 1) :=
      Sobolev.zeroPreservingShiftedRpow_eq (c := c) (p := p - 1) hpos
    rw [ht, sub_add_cancel]
  have hrgrad (i : Fin q) : (W.affineEnergyMap hX T w (c ^ (p - 1)) z :
      GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] fun x => W.toFun x *
        (((p - 1) * ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (p - 2)) *
          (z : GradientSpace (N := N) ⊤ q).snd i x) + W.gradient i x *
            ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (p - 1) := by
    simpa only [show p - 1 - 1 = p - 2 by ring] using
      W.shifted_rpow_affine_gradient_ae hX hc (r := p - 1) (by linarith) z w hz hdw i
  rw [hflux]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [hval, hgrad i, hrval, hrgrad i] with x hv hg hrv hrg
  rw [hrv, hrg]
  by_cases hactive : W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0)
  · obtain ⟨hφ, hk⟩ := hplateau x hactive
    have hzv : (z : GradientSpace (N := N) ⊤ q).fst x = u x := by
      simpa only [hφ, mul_one] using hv
    have hzg : (z : GradientSpace (N := N) ⊤ q).snd i x = g i x := by
      simpa only [hφ, hk, mul_one, mul_zero, add_zero] using hg
    simp only [hφ, hk, hzv, hzg, one_mul, zero_mul, add_zero]
  · have hw : W.toFun x = 0 := not_ne_iff.mp (fun hn => hactive (Or.inl hn))
    have hd : W.gradient i x = 0 := not_ne_iff.mp (fun hn => hactive (Or.inr ⟨i, hn⟩))
    simp only [hw, hd, zero_mul, mul_zero, add_zero]

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicReciprocalGradient
public import HeatKernel.Moser.WeakSolutionCompactSpatialTests
public import HeatKernel.Moser.WeakSolutionAffineEnergyIdentity
import all Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # Restoring the constant in localized reciprocal energy tests -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace HeatKernel

/-- Adding the weight representative restores the literal reciprocal test in the
zero-boundary energy domain, with both horizontal chain and product terms intact. -/
theorem WeakSolutionSpatialWeight.exists_reciprocal_test {N q : ℕ}
    {V : TopologicalSpace.Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {c : ℝ} (hc : 0 < c) (z w : zeroBoundaryGraph V X)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (hdw : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i) :
    ∃ r : zeroBoundaryGraph V X,
      r = W.affineEnergyMap hX (shiftedRpowWeakSolutionTest hc (p := -1) (by norm_num)) w c⁻¹ z ∧
      (r : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => W.toFun x * ((z : GradientSpace (N := N) ⊤ q).fst x + c)⁻¹) ∧
      ∀ i, (r : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => W.toFun x * (-(((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ 2)⁻¹ *
          (z : GradientSpace (N := N) ⊤ q).snd i x) +
          W.gradient i x * ((z : GradientSpace (N := N) ⊤ q).fst x + c)⁻¹) := by
  let P := W.energyMap hX (shiftedRpowWeakSolutionTest hc (p := -1) (by norm_num)) z
  refine ⟨P + c⁻¹ • w, rfl, ?_, ?_⟩
  · have ha := Lp.coeFn_add (P : GradientSpace (N := N) ⊤ q).fst
      (c⁻¹ • (w : GradientSpace (N := N) ⊤ q).fst)
    have hs := Lp.coeFn_smul c⁻¹ (w : GradientSpace (N := N) ⊤ q).fst
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at ha hs
    filter_upwards [ha, hs, W.energyMap_value_ae hX
      (shiftedRpowWeakSolutionTest hc (p := -1) (by norm_num)) z, hw, hz]
      with x hax hsx hpx hwx hzx
    change ((P : GradientSpace (N := N) ⊤ q).fst +
      c⁻¹ • (w : GradientSpace (N := N) ⊤ q).fst) x = _
    rw [hax]
    simp only [Pi.add_apply]
    rw [hsx]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hpx, hwx, shiftedReciprocalWeakSolutionTest_eq hc hzx]
    ring
  · intro i
    have ha := Lp.coeFn_add ((P : GradientSpace (N := N) ⊤ q).snd i)
      (c⁻¹ • (w : GradientSpace (N := N) ⊤ q).snd i)
    have hs := Lp.coeFn_smul c⁻¹ ((w : GradientSpace (N := N) ⊤ q).snd i)
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at ha hs
    filter_upwards [ha, hs, W.reciprocal_energyMap_gradient_ae hX hc z i hz, hdw i]
      with x hax hsx hpx hwx
    change ((P : GradientSpace (N := N) ⊤ q).snd i +
      c⁻¹ • (w : GradientSpace (N := N) ⊤ q).snd i) x = _
    rw [hax]
    simp only [Pi.add_apply]
    rw [hsx]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hpx, hwx]
    ring

end HeatKernel

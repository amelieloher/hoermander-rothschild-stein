-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicMeanEnergyInequality
public import HeatKernel.Moser.LogarithmicReciprocalFlux
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Logarithmic differential inequalities from localized weak coefficient fluxes -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- The reciprocal affine flux gives the logarithmic mean differential inequality
using only the square-integrable zero-boundary gradient. The original solution and
its gradient need no global integrability assumption. -/
theorem WeakSolutionSpatialWeight.logarithmic_mean_deriv_lower_bound {N q : ℕ}
    {V : TopologicalSpace.Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (a : Fin q → Fin q → (Fin N → ℝ) → ℝ)
    {u φ η : (Fin N → ℝ) → ℝ} {g k d : Fin q → (Fin N → ℝ) → ℝ}
    (z w : zeroBoundaryGraph V X) (F : zeroBoundaryGraph V X →L[ℝ] ℝ)
    {c C K mass t : ℝ} {m : ℝ → ℝ} (hc : 0 < c) (hmass : 0 < mass)
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
    (hη : AEStronglyMeasurable η volume) (hηbound : ∀ᵐ x ∂volume, ‖η x‖ ≤ K)
    (hW : W.toFun =ᵐ[volume] fun x => η x ^ 2)
    (hD : ∀ i, W.gradient i =ᵐ[volume] fun x => 2 * η x * d i x)
    (hd : ∀ i, MemLp (d i) 2 volume)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) volume)
    (hb : ∀ i j, ∀ᵐ x ∂volume, ‖a i j x‖ ≤ C)
    (hsym : ∀ᵐ x ∂volume, ∀ i j, a i j x = a j i x)
    (hpos : ∀ᵐ x ∂volume, ∀ ξ, 0 ≤ matrixEnergy (fun i j => a i j x) ξ)
    (hder : HasDerivAt m (mass⁻¹ * (-F (W.affineEnergyMap hX
      (shiftedRpowWeakSolutionTest hc (p := -1) (by norm_num)) w c⁻¹ z))) t) :
    let v := fun i x => η x * (((z : GradientSpace (N := N) ⊤ q).fst x + c)⁻¹ *
      (z : GradientSpace (N := N) ⊤ q).snd i x)
    mass⁻¹ * (∫ x, ∑ i, ∑ j, a i j x * v j x * v i x) / 2 -
      2 * mass⁻¹ * (∫ x, ∑ i, ∑ j, a i j x * d j x * d i x) ≤ deriv m t := by
  have he := W.reciprocal_affine_flux_eq_localized hX a z w F hc hz hw hdw
    hgrad hflux hplateau
  have heq : F (W.affineEnergyMap hX
      (shiftedRpowWeakSolutionTest hc (p := -1) (by norm_num)) w c⁻¹ z) =
      ∑ i, ∫ x, (∑ j, a i j x * (z : GradientSpace (N := N) ⊤ q).snd j x) *
        (η x ^ 2 * (-(((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ 2)⁻¹ *
          (z : GradientSpace (N := N) ⊤ q).snd i x) +
          (2 * η x * d i x) * ((z : GradientSpace (N := N) ⊤ q).fst x + c)⁻¹) := by
    rw [he]
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [hW, hD i] with x hv hg
    rw [hv, hg]
  rw [heq] at hder
  have hu : AEStronglyMeasurable (z : GradientSpace (N := N) ⊤ q).fst volume := by
    simpa only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using
      (Lp.memLp (z : GradientSpace (N := N) ⊤ q).fst).aestronglyMeasurable
  have hg (i : Fin q) : MemLp ((z : GradientSpace (N := N) ⊤ q).snd i) 2 volume := by
    simpa only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp ((z : GradientSpace (N := N) ⊤ q).snd i)
  exact shifted_logarithmic_mean_deriv_lower_bound hc hmass hu hz hη hηbound
    ha hb hg hd hsym hpos hder

end HeatKernel

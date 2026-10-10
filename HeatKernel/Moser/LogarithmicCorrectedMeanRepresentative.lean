-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicMeanEnergyRepresentative
public import HeatKernel.Moser.LogarithmicMeanMonotonicity
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Monotone corrections of weak-solution logarithmic means -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- A uniform bound on the normalized cutoff energy gives a monotone linear
correction of the actual logarithmic mean and bounds its logarithmic energy by
twice the derivative of the corrected mean. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.exists_corrected_logarithmic_mean_of_cutoff_energy_bound
    {N q : ℕ} {V : TopologicalSpace.Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ η : (Fin N → ℝ) → ℝ} {k d : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B a b c C K D : ℝ}
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F)
    (W : WeakSolutionSpatialWeight V X) (w : zeroBoundaryGraph V X)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (hdw : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i)
    (hplateau : ∀ x, W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, k i x = 0)
    (hz : ∀ᵐ t ∂volume.restrict (Icc A B), ∀ᵐ x ∂volume,
      0 ≤ (v t : GradientSpace (N := N) ⊤ q).fst x)
    (hη : AEStronglyMeasurable η volume) (hηbound : ∀ᵐ x ∂volume, ‖η x‖ ≤ K)
    (hW : W.toFun =ᵐ[volume] fun x => η x ^ 2)
    (hD : ∀ i, W.gradient i =ᵐ[volume] fun x => 2 * η x * d i x)
    (hd : ∀ i, MemLp (d i) 2 volume)
    (hcoeff : ∀ᵐ t ∂volume.restrict (Icc A B),
      (∀ i j, AEStronglyMeasurable (fun x => coeff t x i j) volume) ∧
      (∀ i j, ∀ᵐ x ∂volume, ‖coeff t x i j‖ ≤ C) ∧
      (∀ᵐ x ∂volume, ∀ i j, coeff t x i j = coeff t x j i) ∧
      (∀ᵐ x ∂volume, ∀ ξ, 0 ≤ matrixEnergy (fun i j => coeff t x i j) ξ))
    (hcutoff : ∀ᵐ t ∂volume.restrict (Icc A B),
      2 * (∫ x, W.toFun x)⁻¹ *
        (∫ x, ∑ i, ∑ j, coeff t x i j * d j x * d i x) ≤ D)
    (hmass : 0 < ∫ x, W.toFun x)
    (hc : 0 < c) (hab : a ≤ b) (hAa : A < a) (hbB : b < B) :
    let E := fun t => (∫ x, W.toFun x)⁻¹ * ∫ x, ∑ i, ∑ j, coeff t x i j *
      (η x * (((v t : GradientSpace (N := N) ⊤ q).fst x + c)⁻¹ *
        (v t : GradientSpace (N := N) ⊤ q).snd j x)) *
      (η x * (((v t : GradientSpace (N := N) ⊤ q).fst x + c)⁻¹ *
        (v t : GradientSpace (N := N) ⊤ q).snd i x))
    ∃ e : ℝ → ℝ, AbsolutelyContinuousOnInterval e a b ∧
      e =ᵐ[volume.restrict (Icc a b)]
        (fun t => (∫ x, W.toFun x)⁻¹ *
          ∫ x, W.toFun x * (Real.log (u t x + c) - Real.log c)) ∧
      AbsolutelyContinuousOnInterval (fun t => e t + D * t) a b ∧
      MonotoneOn (fun t => e t + D * t) (Icc a b) ∧
      ∀ᵐ t ∂volume.restrict (Icc a b), E t ≤ 2 * deriv (fun s => e s + D * s) t := by
  let E := fun t => (∫ x, W.toFun x)⁻¹ * ∫ x, ∑ i, ∑ j, coeff t x i j *
    (η x * (((v t : GradientSpace (N := N) ⊤ q).fst x + c)⁻¹ *
      (v t : GradientSpace (N := N) ⊤ q).snd j x)) *
    (η x * (((v t : GradientSpace (N := N) ⊤ q).fst x + c)⁻¹ *
      (v t : GradientSpace (N := N) ⊤ q).snd i x))
  obtain ⟨e, hac, heq, hineq⟩ := hp.exists_logarithmic_mean_energy_representative hX W w
    hw hdw hplateau hz hη hηbound hW hD hd hcoeff hmass hc hab hAa hbB
  have hsub : Icc a b ⊆ Icc A B := fun t ht =>
    ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  have hAB : A ≤ B := (hAa.le.trans hab).trans hbB.le
  have hac' : AbsolutelyContinuousOnInterval e a b := hac.mono (by
    rw [uIcc_of_le hab, uIcc_of_le hAB]
    exact hsub)
  have hnonneg : ∀ᵐ t ∂volume.restrict (Icc A B), 0 ≤ E t := by
    filter_upwards [hcoeff] with t ht
    apply mul_nonneg (inv_nonneg.mpr hmass.le)
    apply integral_nonneg_of_ae
    filter_upwards [ht.2.2.2] with x hx
    exact hx (fun i => η x * (((v t : GradientSpace (N := N) ⊤ q).fst x + c)⁻¹ *
      (v t : GradientSpace (N := N) ⊤ q).snd i x))
  have hbound : ∀ᵐ t ∂volume.restrict (Icc A B), E t / 2 - D ≤ deriv e t := by
    filter_upwards [hineq, hcutoff] with t hi hc
    dsimp only [E] at hi ⊢
    linarith
  have hE : ∀ᵐ t ∂volume, t ∈ uIcc a b → 0 ≤ E t := by
    rw [uIcc_of_le hab]
    exact (ae_restrict_iff' measurableSet_Icc).mp
      (ae_restrict_of_ae_restrict_of_subset hsub hnonneg)
  have hI : ∀ᵐ t ∂volume, t ∈ uIcc a b → E t / 2 - D ≤ deriv e t := by
    rw [uIcc_of_le hab]
    exact (ae_restrict_iff' measurableSet_Icc).mp
      (ae_restrict_of_ae_restrict_of_subset hsub hbound)
  obtain ⟨hgc, hgm, hge⟩ := logarithmic_mean_correction hac' hE hI
  refine ⟨e, hac', heq, hgc, ?_, ?_⟩
  · simpa only [uIcc_of_le hab] using hgm
  · apply (ae_restrict_iff' measurableSet_Icc).mpr
    simpa only [uIcc_of_le hab] using hge

end HeatKernel

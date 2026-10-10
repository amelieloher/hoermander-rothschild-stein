-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicMeanRepresentative
public import HeatKernel.Moser.LogarithmicLocalizedEnergyInequality
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Logarithmic energy inequalities for absolutely continuous weak-solution means -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- The weak cutoff equation supplies an absolutely continuous representative of
the literal logarithmic mean and its logarithmic energy inequality almost
everywhere. The cutoff energy remains explicit. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.exists_logarithmic_mean_energy_representative
    {N q : ℕ} {V : TopologicalSpace.Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ η : (Fin N → ℝ) → ℝ} {k d : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B a b c C K : ℝ}
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
    (hmass : 0 < ∫ x, W.toFun x)
    (hc : 0 < c) (hab : a ≤ b) (hAa : A < a) (hbB : b < B) :
    ∃ e : ℝ → ℝ, AbsolutelyContinuousOnInterval e A B ∧
      e =ᵐ[volume.restrict (Icc a b)]
        (fun t => (∫ x, W.toFun x)⁻¹ *
          ∫ x, W.toFun x * (Real.log (u t x + c) - Real.log c)) ∧
      ∀ᵐ t ∂volume.restrict (Icc A B),
        let z := fun i x => η x * (((v t : GradientSpace (N := N) ⊤ q).fst x + c)⁻¹ *
          (v t : GradientSpace (N := N) ⊤ q).snd i x)
        (∫ x, W.toFun x)⁻¹ * (∫ x, ∑ i, ∑ j, coeff t x i j * z j x * z i x) / 2 -
          2 * (∫ x, W.toFun x)⁻¹ *
            (∫ x, ∑ i, ∑ j, coeff t x i j * d j x * d i x) ≤ deriv e t := by
  have hupos : ∀ᵐ t ∂volume.restrict (Icc A B), ∀ᵐ x ∂volume,
      W.toFun x ≠ 0 → 0 ≤ u t x := by
    filter_upwards [hz, hp.2.2.1] with t ht hv
    filter_upwards [ht, hv] with x hx hv hactive
    have hφ := (hplateau x (Or.inl hactive)).1
    rw [hv, hφ, mul_one] at hx
    exact hx
  obtain ⟨e, hac, heq, hder⟩ := hp.exists_logarithmic_mean_representative hX W w hw
    (fun x hx => (hplateau x (Or.inl hx)).1) hupos hc hab hAa hbB
  refine ⟨e, hac, heq, ?_⟩
  filter_upwards [ae_restrict_of_ae hder, ae_restrict_mem measurableSet_Icc,
    hz, ae_all_iff.mpr hp.2.2.2.1, hp.2.2.2.2.2.1, hcoeff] with t ht hmem hz hg hf ha
  exact W.logarithmic_mean_deriv_lower_bound hX (fun i j x => coeff t x i j)
    (v t) w (F t) hc hmass hz hw hdw hg hf hplateau hη hηbound hW hD hd
    ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 (ht hmem)

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicAffineEndpoints
public import HeatKernel.Moser.WeakSolutionAffineTimeTesting
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Absolutely continuous representatives of local weighted logarithmic energies -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- The original weak cutoff equation supplies a locally absolutely continuous
weighted logarithmic mean. Its derivative is the negative original restored
reciprocal flux, with no assumed time regularity of the logarithmic integral. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.exists_logarithmic_mean_representative
    {N q : ℕ} {V : TopologicalSpace.Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B a b c : ℝ}
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F)
    (W : WeakSolutionSpatialWeight V X) (w : zeroBoundaryGraph V X)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (hplateau : ∀ x, W.toFun x ≠ 0 → φ x = 1)
    (hupos : ∀ᵐ t ∂volume.restrict (Icc A B), ∀ᵐ x ∂volume,
      W.toFun x ≠ 0 → 0 ≤ u t x)
    (hc : 0 < c) (hab : a ≤ b) (hAa : A < a) (hbB : b < B) :
    ∃ e : ℝ → ℝ, AbsolutelyContinuousOnInterval e A B ∧
      e =ᵐ[volume.restrict (Icc a b)]
        (fun t => (∫ x, W.toFun x)⁻¹ *
          ∫ x, W.toFun x * (Real.log (u t x + c) - Real.log c)) ∧
      (∀ᵐ t ∂volume, t ∈ Icc A B → HasDerivAt e
        ((∫ x, W.toFun x)⁻¹ * (-F t (W.affineEnergyMap hX
          (shiftedRpowWeakSolutionTest hc (p := -1) (by norm_num)) w c⁻¹ (v t)))) t) := by
  obtain ⟨e, hac, heq, hder⟩ := hp.exists_affine_energy_representative hX W
    (shiftedRpowWeakSolutionTest hc (p := -1) (by norm_num)) w c⁻¹ hab hAa hbB
  refine ⟨fun t => (∫ x, W.toFun x)⁻¹ * e t,
    AbsolutelyContinuousOnInterval.const_mul _ hac, ?_, ?_⟩
  · have hsub : Icc a b ⊆ Icc A B := fun t ht =>
      ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
    filter_upwards [heq, ae_restrict_of_ae_restrict_of_subset hsub hp.2.2.1,
      ae_restrict_of_ae_restrict_of_subset hsub hupos] with t he hv ht
    rw [he, W.reciprocal_affineEnergy_eq_integral_of_plateau hc w hw (v t) hv hplateau ht]
  · filter_upwards [hder] with t ht hmem
    exact (ht hmem).const_mul _

end HeatKernel

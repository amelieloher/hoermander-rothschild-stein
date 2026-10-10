-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CompactEnergyMultipliers
public import HeatKernel.Form.CompactZeroBoundary
public import HeatKernel.Form.LocalEnergyAlgebra
import Mathlib.Tactic.Linter

/-! # Smooth compact multipliers into zero-boundary energy spaces -/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter TopologicalSpace RothschildStein

namespace HeatKernel

/-- Every smooth compact cutoff defines a continuous multiplier into its zero-boundary domain. -/
theorem exists_smooth_compact_zeroBoundary_multiplier {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {φ : (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ (U : Set (Fin N → ℝ))) :
    ∃ M : energyGraph (N := N) ⊤ X →L[ℝ] zeroBoundaryGraph U X,
      ∀ w, (M w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => φ x * (w : GradientSpace (N := N) ⊤ q).fst x) ∧
      ∀ i, (M w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        fun x => φ x * (w : GradientSpace (N := N) ⊤ q).snd i x +
          fieldDerivative (X i) φ x * (w : GradientSpace (N := N) ⊤ q).fst x := by
  have hD : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (X i) φ) := fun i => by
    simpa only [Opens.coe_top, contDiffOn_univ] using
      S.contDiffOn_fieldDerivative ⊤ (X i) φ (hX i).contDiffOn hφ.contDiffOn
  have hcD : ∀ i, HasCompactSupport (fieldDerivative (X i) φ) := fun i =>
    hc.of_isClosed_subset (isClosed_tsupport _) (S.tsupport_fieldDerivative_subset (X i) φ)
  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hφ.continuous
  choose B hB using fun i => (hcD i).exists_bound_of_continuous (hD i).continuous
  have hAp : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hBp : ∀ i, 0 ≤ B i := fun i => (norm_nonneg _).trans (hB i 0)
  have hsum : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ => hBp i
  have hb : ∀ i, ∀ᵐ x ∂volume, ‖fieldDerivative (X i) φ x‖ ≤ ∑ j, B j := fun i =>
    Eventually.of_forall fun x => (hB i x).trans
      (Finset.single_le_sum (fun j _ => hBp j) (Finset.mem_univ i))
  obtain ⟨M, hM⟩ := exists_energyMultiplierLinearMap X hX
    (memLocalEnergy_of_contDiff ⊤ X hX hφ)
    (fun i => by simpa only [wordDerivative, Function.comp_def] using
      S.hasWeakWordDeriv_classical ⊤ X (fun j => (hX j).contDiffOn) [i] φ hφ.contDiffOn)
    hAp hsum (Eventually.of_forall hA) hb
  let M₀ := compactEnergyMultiplier U X hX hc hs M (fun w => (hM w).1)
  exact ⟨M₀, fun w => ⟨(hM w).1, (hM w).2⟩⟩

/-- Every constant multiple of a smooth compact cutoff has a zero-boundary energy representative. -/
theorem exists_zeroBoundaryGraph_smooth_compact_constant {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {φ : (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ (U : Set (Fin N → ℝ))) (a : ℝ) :
    ∃ c : zeroBoundaryGraph U X,
      (c : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] (fun x => φ x * a) ∧
      ∀ i, (c : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        fun x => fieldDerivative (X i) φ x * a := by
  obtain ⟨v, hv, hvf, hvg⟩ := exists_interiorGradientPair U X hφ hc hs hX
  let c : zeroBoundaryGraph U X := a • (⟨v, interiorGradientPairs_subset_zeroBoundaryGraph U X hv⟩ :
    zeroBoundaryGraph U X)
  refine ⟨c, ?_, fun i => ?_⟩
  · have h := Lp.coeFn_smul a v.fst
    simp only [Opens.coe_top, Measure.restrict_univ] at h
    filter_upwards [h, hvf] with x hx he
    change (a • v.fst) x = _
    simpa only [Pi.smul_apply, he, smul_eq_mul, mul_comm] using hx
  · have h := Lp.coeFn_smul a (v.snd i)
    simp only [Opens.coe_top, Measure.restrict_univ] at h
    filter_upwards [h, hvg i] with x hx he
    change (a • v.snd i) x = _
    simpa only [Pi.smul_apply, he, smul_eq_mul, mul_comm] using hx


end HeatKernel

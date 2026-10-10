-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.PointwiseContractions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linter

/-! # Lipschitz scalar calculus with pointwise horizontal energy bounds -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped NNReal

namespace HeatKernel

/-- Positive normalization turns a scalar Lipschitz map into a normal contraction. -/
theorem lipschitzWith_normalized {L : ℝ≥0} {η : ℝ → ℝ}
    (hη : LipschitzWith L η) (hL : 0 < (L : ℝ)) :
    LipschitzWith 1 (fun s => (L : ℝ)⁻¹ * η s) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hL), NNReal.coe_one, one_mul]
  calc
    _ ≤ (L : ℝ)⁻¹ * ((L : ℝ) * |s - t|) :=
      mul_le_mul_of_nonneg_left (hη.dist_le_mul s t) (inv_nonneg.mpr hL.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]

/-- Scalar multiplication multiplies horizontal energy density by the squared scalar. -/
theorem horizontalEnergyDensity_smul_ae {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (u : energyGraph (N := N) ⊤ X) (c : ℝ) :
    horizontalEnergyDensity ⊤ X (c • u) (c • u) =ᵐ[volume]
      (fun x => c ^ 2 * horizontalEnergyDensity ⊤ X u u x) := by
  have hg : ∀ i, ((c • u : energyGraph (N := N) ⊤ X) : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      (fun x => c * (u : GradientSpace (N := N) ⊤ q).snd i x) := by
    intro i
    simpa only [Submodule.coe_smul, WithLp.smul_snd, PiLp.smul_apply, Pi.smul_def,
      smul_eq_mul, Opens.coe_top, Measure.restrict_univ] using
      Lp.coeFn_smul c ((u : GradientSpace (N := N) ⊤ q).snd i)
  filter_upwards [ae_all_iff.mpr hg] with x hx
  unfold horizontalEnergyDensity
  simp only [hx, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every Lipschitz scalar map fixing zero preserves the global energy domain and satisfies
the exact squared Lipschitz bound for its horizontal energy density. -/
theorem exists_energyGraph_comp_lipschitz_density_le {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u : energyGraph (N := N) ⊤ X)
    {L : ℝ≥0} {η : ℝ → ℝ} (hη : LipschitzWith L η) (hzero : η 0 = 0) :
    ∃ z : energyGraph (N := N) ⊤ X,
      (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => η ((u : GradientSpace (N := N) ⊤ q).fst x)) ∧
      ∀ᵐ x ∂volume, horizontalEnergyDensity ⊤ X z z x ≤
        (L : ℝ) ^ 2 * horizontalEnergyDensity ⊤ X u u x := by
  by_cases hL : (L : ℝ) = 0
  · have heta : ∀ s, η s = 0 := by
      intro s
      have H := hη.dist_le_mul s 0
      simpa only [hL, hzero, zero_mul, dist_zero_right, norm_le_zero_iff] using H
    refine ⟨0, ?_, ?_⟩
    · simpa only [Submodule.coe_zero, WithLp.zero_fst, Opens.coe_top, Measure.restrict_univ, Pi.zero_def, heta] using
        Lp.coeFn_zero ℝ 2 (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))
    · have H := horizontalEnergyDensity_smul_ae X u 0
      filter_upwards [H] with x hx
      simpa only [zero_smul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, hL] using hx.le
  · have hLp : 0 < (L : ℝ) := lt_of_le_of_ne L.coe_nonneg (Ne.symm hL)
    let τ : ℝ → ℝ := fun s => (L : ℝ)⁻¹ * η s
    have hτ := lipschitzWith_normalized hη hLp
    have hτ0 : τ 0 = 0 := by simp only [τ, hzero, mul_zero]
    obtain ⟨w, hw, he⟩ := exists_energyGraph_comp_normalContraction_density_le X hX u hτ hτ0
    have hwf : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => τ ((u : GradientSpace (N := N) ⊤ q).fst x)) := by
      have H := hτ.coeFn_compLp hτ0 (energyInclusion ⊤ X u)
      rw [← hw] at H
      change (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict
        ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))]
        (fun x => τ ((u : GradientSpace (N := N) ⊤ q).fst x)) at H
      simpa only [Opens.coe_top, Measure.restrict_univ] using H
    refine ⟨(L : ℝ) • w, ?_, ?_⟩
    · have H : (((L : ℝ) • w : energyGraph (N := N) ⊤ X) : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
          (fun x => (L : ℝ) * (w : GradientSpace (N := N) ⊤ q).fst x) := by
        simpa only [Submodule.coe_smul, WithLp.smul_fst, Pi.smul_def, smul_eq_mul,
          Opens.coe_top, Measure.restrict_univ] using
          Lp.coeFn_smul (L : ℝ) (w : GradientSpace (N := N) ⊤ q).fst
      filter_upwards [H, hwf] with x hx hwx
      rw [hx, hwx]
      dsimp only [τ]
      rw [← mul_assoc, mul_inv_cancel₀ hL, one_mul]
    · filter_upwards [horizontalEnergyDensity_smul_ae X w (L : ℝ), he] with x hx hxe
      rw [hx]
      exact mul_le_mul_of_nonneg_left hxe (sq_nonneg _)



end HeatKernel

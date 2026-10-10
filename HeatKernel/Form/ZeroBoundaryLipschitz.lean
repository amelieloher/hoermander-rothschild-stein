-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LipschitzCalculus
public import HeatKernel.Form.ZeroBoundaryContractions
import Mathlib.Tactic.Linter

/-! # Lipschitz scalar maps on zero-boundary horizontal energy domains -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped NNReal

namespace HeatKernel

/-- Every scalar Lipschitz map fixing zero preserves every zero-boundary horizontal domain. -/
theorem exists_zeroBoundaryGraph_comp_lipschitz {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u : zeroBoundaryGraph U X)
    {L : ℝ≥0} {η : ℝ → ℝ} (hη : LipschitzWith L η) (hzero : η 0 = 0) :
    ∃ z : energyGraph (N := N) ⊤ X,
      (z : GradientSpace (N := N) ⊤ q) ∈ zeroBoundaryGraph U X ∧
      (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => η ((u : GradientSpace (N := N) ⊤ q).fst x)) := by
  let M : ℝ≥0 := max L 1
  have hMp : 0 < (M : ℝ) := lt_of_lt_of_le zero_lt_one (by
    exact_mod_cast (le_max_right L 1))
  let τ : ℝ → ℝ := fun s => (M : ℝ)⁻¹ * η s
  have hτ : LipschitzWith 1 τ := lipschitzWith_normalized (hη.weaken (le_max_left L 1)) hMp
  have hτ0 : τ 0 = 0 := by simp only [τ, hzero, mul_zero]
  obtain ⟨w, hwmem, hw⟩ := exists_zeroBoundaryGraph_comp_normalContraction U X hX u hτ hτ0
  have hwf : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      (fun x => τ ((u : GradientSpace (N := N) ⊤ q).fst x)) := by
    have H := hτ.coeFn_compLp hτ0 (u : GradientSpace (N := N) ⊤ q).fst
    rw [← hw] at H
    change (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict
      ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))]
      (fun x => τ ((u : GradientSpace (N := N) ⊤ q).fst x)) at H
    simpa only [Opens.coe_top, Measure.restrict_univ] using H
  refine ⟨(M : ℝ) • w, (zeroBoundaryGraph U X).smul_mem (M : ℝ) hwmem, ?_⟩
  have hz : (((M : ℝ) • w : energyGraph (N := N) ⊤ X) : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      (fun x => (M : ℝ) * (w : GradientSpace (N := N) ⊤ q).fst x) := by
    simpa only [Submodule.coe_smul, WithLp.smul_fst, Pi.smul_def, smul_eq_mul,
      Opens.coe_top, Measure.restrict_univ] using
      Lp.coeFn_smul (M : ℝ) (w : GradientSpace (N := N) ⊤ q).fst
  filter_upwards [hz, hwf] with x hx hwx
  rw [hx, hwx]
  dsimp only [τ]
  rw [← mul_assoc, mul_inv_cancel₀ hMp.ne', one_mul]

end HeatKernel

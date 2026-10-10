-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ZeroBoundaryLipschitz
import Mathlib.Tactic.Linter

/-! # Zero-boundary membership of nonlinear energy representatives -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace

open scoped NNReal ENNReal

namespace HeatKernel

/-- Any energy representative of a Lipschitz scalar composition fixing zero belongs to the
same zero-boundary domain as its original function. -/
theorem mem_zeroBoundaryGraph_of_lipschitz_composition {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u z : energyGraph (N := N) ⊤ X)
    (hu : (u : GradientSpace (N := N) ⊤ q) ∈ zeroBoundaryGraph U X)
    {L : ℝ≥0} {η : ℝ → ℝ} (hη : LipschitzWith L η) (hzero : η 0 = 0)
    (hz : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => η ((u : GradientSpace (N := N) ⊤ q).fst x)) :
    (z : GradientSpace (N := N) ⊤ q) ∈ zeroBoundaryGraph U X := by
  obtain ⟨w, hw, hwf⟩ := exists_zeroBoundaryGraph_comp_lipschitz U X hX ⟨u, hu⟩ hη hzero
  have he : z = w := by
    apply energyInclusion_injective ⊤ X (fun i => (hX i).contDiffOn)
    apply Lp.ext
    change (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict (⊤ : Opens (Fin N → ℝ))]
      (w : GradientSpace (N := N) ⊤ q).fst
    simpa only [Opens.coe_top, Measure.restrict_univ] using hz.trans hwf.symm
  simpa only [he] using hw



end HeatKernel

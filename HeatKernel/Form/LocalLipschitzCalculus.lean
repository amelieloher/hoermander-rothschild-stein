-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LipschitzCalculus
public import HeatKernel.Form.LocalEnergy
import Mathlib.Tactic.Linter

/-! # Lipschitz scalar maps on local horizontal energy domains -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped NNReal

namespace HeatKernel

/-- Lipschitz scalar maps fixing zero preserve the local horizontal energy domain. -/
theorem MemLocalEnergy.comp_lipschitz {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {f : (Fin N → ℝ) → ℝ}
    (hf : MemLocalEnergy U X f) {L : ℝ≥0} {η : ℝ → ℝ}
    (hη : LipschitzWith L η) (hzero : η 0 = 0) : MemLocalEnergy U X (η ∘ f) := by
  refine ⟨hη.continuous.comp_aestronglyMeasurable hf.1, fun V hVc hVU => ?_⟩
  obtain ⟨w, hw⟩ := hf.2 V hVc hVU
  obtain ⟨z, hz, _⟩ := exists_energyGraph_comp_lipschitz_density_le X hX w hη hzero
  have hzV : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict (V : Set (Fin N → ℝ))]
      η ∘ (w : GradientSpace (N := N) ⊤ q).fst := ae_restrict_of_ae hz
  exact ⟨z, hzV.trans (hw.fun_comp η)⟩

end HeatKernel

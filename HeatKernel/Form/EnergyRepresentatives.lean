-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.GraphForm
import Mathlib.Tactic.Linter

/-! # Uniqueness of energy vectors from their scalar representatives -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace HeatKernel

/-- Almost everywhere equality of scalar representatives determines a closed energy vector. -/
theorem energyGraph_ext_of_ae {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    {u v : energyGraph U X}
    (h : energyInclusion U X u =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] energyInclusion U X v) :
    u = v := energyInclusion_injective U X hX (Lp.ext h)

end HeatKernel

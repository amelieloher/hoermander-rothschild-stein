-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.GradientCurves
public import HeatKernel.Form.ProductL2

/-!
# Bochner square integrability of energy curves

Product square integrability of a function and its weak-gradient representatives gives square
integrability in the energy graph, once the spatial graph membership is known.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace HeatKernel

/-- Componentwise product L² bounds imply Bochner L² membership of an energy-graph curve. -/
theorem memLp_energyGraph_of_product_representatives {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {N q : ℕ} {U : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {v : α → energyGraph U X}
    {u : α → (Fin N → ℝ) → ℝ} {g : Fin q → α → (Fin N → ℝ) → ℝ}
    (hu : MemLp (Function.uncurry u) 2 (μ.prod (volume.restrict (U : Set (Fin N → ℝ)))))
    (hg : ∀ i, MemLp (Function.uncurry (g i)) 2 (μ.prod (volume.restrict (U : Set (Fin N → ℝ)))))
    (hvu : ∀ᵐ a ∂μ, (v a : GradientSpace U q).fst =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] u a)
    (hvg : ∀ i, ∀ᵐ a ∂μ, (v a : GradientSpace U q).snd i =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] g i a) :
    MemLp v 2 μ := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let : IsSeparable (volume.restrict (U : Set (Fin N → ℝ))) := isSeparable_of_sigmaFinite _
  rw [memLp_energyGraph_iff]
  exact ⟨memLp_L2_of_product_representatives hu hvu,
    fun i => memLp_L2_of_product_representatives (hg i) (hvg i)⟩

end HeatKernel

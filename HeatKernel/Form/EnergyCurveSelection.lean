-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.EnergyCurves
import Mathlib.Tactic.Linter

/-! # Selection of Bochner energy curves from joint representatives -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace HeatKernel

/-- Almost-everywhere spatial energy membership and product square integrability produce a
Bochner square integrable energy curve with the prescribed function and gradient. -/
theorem exists_energyGraph_curve_of_ae_representatives {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (u : α → (Fin N → ℝ) → ℝ) (g : Fin q → α → (Fin N → ℝ) → ℝ)
    (hu : MemLp (Function.uncurry u) 2 (μ.prod (volume.restrict (U : Set (Fin N → ℝ)))))
    (hg : ∀ i, MemLp (Function.uncurry (g i)) 2 (μ.prod (volume.restrict (U : Set (Fin N → ℝ)))))
    (hw : ∀ᵐ t ∂μ, ∃ w : energyGraph U X,
      (w : GradientSpace U q).fst =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] u t ∧
      ∀ i, (w : GradientSpace U q).snd i =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] g i t) :
    ∃ v : α → energyGraph U X, MemLp v 2 μ ∧
      (∀ᵐ t ∂μ, (v t : GradientSpace U q).fst =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] u t) ∧
      ∀ i, ∀ᵐ t ∂μ, (v t : GradientSpace U q).snd i =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] g i t := by
  classical
  let P := fun t (w : energyGraph U X) =>
    (w : GradientSpace U q).fst =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] u t ∧
      ∀ i, (w : GradientSpace U q).snd i =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] g i t
  let v : α → energyGraph U X := fun t => if h : ∃ w, P t w then Classical.choose h else 0
  have hv : ∀ᵐ t ∂μ, P t (v t) := by
    filter_upwards [hw] with t ht
    dsimp only [v]
    rw [dite_eq_left ht]
    exact Classical.choose_spec ht
  have hvu := hv.mono fun _ ht => ht.1
  have hvg := fun i => hv.mono fun _ ht => ht.2 i
  exact ⟨v, memLp_energyGraph_of_product_representatives hu hg hvu hvg, hvu, hvg⟩



end HeatKernel

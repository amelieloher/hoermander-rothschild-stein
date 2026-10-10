-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ZeroBoundaryCompositionRepresentatives
import Mathlib.Tactic.Linter

/-! # Bochner curves valued in zero-boundary energy domains -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace

open scoped NNReal ENNReal

namespace HeatKernel

/-- An energy curve almost everywhere in a zero-boundary domain has a Bochner representative
valued in that Hilbert subspace, with the identical ambient graph pair almost everywhere. -/
theorem exists_zeroBoundaryGraph_curve_of_ae_mem {T : Type*} [MeasurableSpace T]
    {μ : Measure T} {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) {p : ℝ≥0∞}
    (v : T → energyGraph (N := N) ⊤ X) (hv : MemLp v p μ)
    (hm : ∀ᵐ t ∂μ, (v t : GradientSpace (N := N) ⊤ q) ∈ zeroBoundaryGraph U X) :
    ∃ w : T → zeroBoundaryGraph U X, MemLp w p μ ∧
      ∀ᵐ t ∂μ, (w t : GradientSpace (N := N) ⊤ q) = (v t : GradientSpace (N := N) ⊤ q) := by
  classical
  let w : T → zeroBoundaryGraph U X := fun t =>
    if ht : (v t : GradientSpace (N := N) ⊤ q) ∈ zeroBoundaryGraph U X
    then ⟨v t, ht⟩ else 0
  have he : ∀ᵐ t ∂μ, (w t : GradientSpace (N := N) ⊤ q) = (v t : GradientSpace (N := N) ⊤ q) := by
    filter_upwards [hm] with t ht
    simp only [w, dite_eq_left ht]
  have ha : AEStronglyMeasurable (fun t => (w t : GradientSpace (N := N) ⊤ q)) μ :=
    ((energyGraph ⊤ X).subtypeL.continuous.comp_aestronglyMeasurable hv.aestronglyMeasurable).congr (by filter_upwards [he] with t ht; exact ht.symm)
  have hw : AEStronglyMeasurable w μ :=
    (Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff).mp ha
  refine ⟨w, hv.of_le hw ?_, he⟩
  filter_upwards [he] with t ht
  change ‖(w t : GradientSpace (N := N) ⊤ q)‖ ≤ ‖(v t : GradientSpace (N := N) ⊤ q)‖
  exact le_of_eq (congrArg norm ht)

end HeatKernel

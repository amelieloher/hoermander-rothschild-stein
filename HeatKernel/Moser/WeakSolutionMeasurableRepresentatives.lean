-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionRepresentativeCongruence
import Mathlib.Tactic

/-! # Measurable representatives of local weak solutions

The product almost-everywhere class of a local weak solution contains a globally
measurable function satisfying the same local equation. If the solution is
nonnegative almost everywhere, the representative can be chosen nonnegative
everywhere without changing its values almost everywhere on the cylinder.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

variable {N q : ℕ} {G : HomogeneousGroup N} {hq : q ≤ N} {hqpos : 0 < q}
  {hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1}
  {hspan : bracketSpansOn univ (G.horizontalFields hq)}
  {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
  {I : Opens ℝ} {U : Opens (Fin N → ℝ)} {u : ℝ → (Fin N → ℝ) → ℝ}

/-- A local weak solution has a jointly measurable representative that remains
a local weak solution on the same cylinder, with the same coefficients. -/
theorem IsLocalWeakSolution.exists_measurable_representative
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u) :
    ∃ v : ℝ × (Fin N → ℝ) → ℝ, Measurable v ∧
      (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) =ᵐ[
        volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))] v ∧
      IsLocalWeakSolution G hq hqpos hw hspan a I U (fun t x => v (t, x)) := by
  let v : ℝ × (Fin N → ℝ) → ℝ := hu.1.mk (fun z => u z.1 z.2)
  have he : (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) =ᵐ[
      volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))] v := hu.1.ae_eq_mk
  exact ⟨v, hu.1.stronglyMeasurable_mk.measurable, he, hu.congr_ae he⟩

/-- An almost-everywhere nonnegative local weak solution has a globally
nonnegative measurable representative satisfying the same local equation. -/
theorem IsLocalWeakSolution.exists_nonnegative_measurable_representative
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u)
    (hn : ∀ᵐ z ∂volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))),
      0 ≤ u z.1 z.2) :
    ∃ v : ℝ × (Fin N → ℝ) → ℝ, Measurable v ∧ (∀ z, 0 ≤ v z) ∧
      (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) =ᵐ[
        volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))] v ∧
      IsLocalWeakSolution G hq hqpos hw hspan a I U (fun t x => v (t, x)) := by
  obtain ⟨w, hwm, huw, _⟩ := hu.exists_measurable_representative
  let v : ℝ × (Fin N → ℝ) → ℝ := fun z => max (w z) 0
  have huv : (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) =ᵐ[
      volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))] v := by
    filter_upwards [huw, hn] with z hz hnonneg
    exact hz.trans (max_eq_left (hz ▸ hnonneg)).symm
  exact ⟨v, hwm.max measurable_const, fun z => le_max_right (w z) 0,
    huv, hu.congr_ae huv⟩

end HeatKernel

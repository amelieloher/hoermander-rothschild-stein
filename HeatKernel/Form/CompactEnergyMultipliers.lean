-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.EssentialSupportZeroBoundary
public import HeatKernel.Form.BoundedEnergyMultiplication
import Mathlib.Tactic.Linter

/-! # Compact energy multipliers with values in zero-boundary domains -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))

include hX in
/-- Any energy representative of a compact multiplier product has zero boundary values on
an open set containing the multiplier's support. -/
theorem mem_zeroBoundaryGraph_of_compact_multiplier
    (z : energyGraph (N := N) ⊤ X) {φ f : (Fin N → ℝ) → ℝ}
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hz : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] fun x => φ x * f x) :
    (z : GradientSpace (N := N) ⊤ q) ∈ zeroBoundaryGraph U X := by
  apply mem_zeroBoundaryGraph_of_ae_zero_off_compact U X hX z hc hs
  filter_upwards [hz] with x hx hn
  rw [hx, image_eq_zero_of_notMem_tsupport hn, zero_mul]

variable {φ : (Fin N → ℝ) → ℝ} (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (M : energyGraph (N := N) ⊤ X →L[ℝ] energyGraph (N := N) ⊤ X)
    (hM : ∀ u, (M u : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => φ x * (u : GradientSpace (N := N) ⊤ q).fst x)

/-- A compactly supported energy multiplier acts continuously into the zero-boundary domain. -/
def compactEnergyMultiplier : energyGraph (N := N) ⊤ X →L[ℝ] zeroBoundaryGraph U X :=
  ((energyGraph (N := N) ⊤ X).subtypeL.comp M).codRestrict (zeroBoundaryGraph U X)
    (fun u => mem_zeroBoundaryGraph_of_compact_multiplier U X hX (M u) hc hs (hM u))

end HeatKernel

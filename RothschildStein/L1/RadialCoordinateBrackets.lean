-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RadialBracketDifferentiation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- The differentiated radial identity in ordinary coordinate directions,
with the derivative of every varying coefficient displayed. -/
theorem radial_frame_bracket_identity {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (Z : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    (hrad : ∀ u ∈ Ω, ∑ i, u i • Z i u = u)
    (V : (Fin N → ℝ) → (Fin N → ℝ)) {u : Fin N → ℝ} (hu : u ∈ Ω) (i : Fin N) :
    VectorField.lieBracket ℝ V (fun _ => Pi.single i 1) u =
      VectorField.lieBracket ℝ V (Z i) u +
      (∑ k, V u k • VectorField.lieBracket ℝ (fun _ => Pi.single i 1) (Z k) u) +
      ∑ k, u k • VectorField.lieBracket ℝ V
        (VectorField.lieBracket ℝ (fun _ => Pi.single i 1) (Z k)) u := by
  have hh := radial_bracket_differential_identity Ω
    (fun k => (ContinuousLinearMap.proj k : (Fin N → ℝ) →L[ℝ] ℝ)) Z hZ hrad V hu (Pi.single i 1)
  simpa [Pi.single_apply] using hh
end RothschildStein.L1

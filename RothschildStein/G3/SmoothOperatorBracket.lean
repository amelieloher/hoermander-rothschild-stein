-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.SmoothFunctionOperators
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.G3

/-- The field-to-operator map preserves the Lie bracket on the actual
open coefficient domain (BB (9.9)–(9.10), pp. 410–411). -/
theorem smoothFieldOperator_lieBracket {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (U V : (Fin N → ℝ) → (Fin N → ℝ))
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U Ω) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω) :
    smoothFieldOperator Ω (VectorField.lieBracket ℝ U V)
      (G1.bracket_contDiffOn Ω.isOpen hU hV) =
      ⁅smoothFieldOperator Ω U hU, smoothFieldOperator Ω V hV⁆ := by
  classical
  rw [Ring.lie_def]
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change (smoothFieldOperator Ω (VectorField.lieBracket ℝ U V) _ f).val x =
    (smoothFieldOperator Ω U hU (smoothFieldOperator Ω V hV f)).val x -
    (smoothFieldOperator Ω V hV (smoothFieldOperator Ω U hU f)).val x
  by_cases hx : x ∈ Ω
  · have heU : (smoothFieldOperator Ω U hU f).val =ᶠ[𝓝 x] fieldDerivative U f.val := by
      filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
      exact smoothFieldOperator_apply Ω U hU f hy
    have heV : (smoothFieldOperator Ω V hV f).val =ᶠ[𝓝 x] fieldDerivative V f.val := by
      filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
      exact smoothFieldOperator_apply Ω V hV f hy
    rw [smoothFieldOperator_apply Ω _ _ f hx,
      smoothFieldOperator_apply Ω U hU _ hx, smoothFieldOperator_apply Ω V hV _ hx,
      G1.bracket_derivative Ω.isOpen hU hV f.property hx]
    unfold fieldDerivative
    rw [heU.fderiv_eq, heV.fderiv_eq]
    rfl
  · change (if x ∈ Ω then _ else (0 : ℝ)) =
      (if x ∈ Ω then _ else (0 : ℝ)) - (if x ∈ Ω then _ else (0 : ℝ))
    simp only [ite_eq_right hx, sub_self]
end RothschildStein.G3

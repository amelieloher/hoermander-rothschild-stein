-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FlowPullbackJets
public import RothschildStein.G3.SmoothFunctionOperators
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.G3

/-- Associativity of repeated application also gives the outer
field-derivative recursion (BB (9.9), p. 411). -/
theorem fieldPower_succ {N : ℕ} (V : (Fin N → ℝ) → (Fin N → ℝ))
    (n : ℕ) (f : (Fin N → ℝ) → ℝ) :
    fieldPower V (n + 1) f = fieldDerivative V (fieldPower V n f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    change fieldPower V (n + 1) (fieldDerivative V f) = _
    rw [ih]
    rfl

/-- Powers in the associative differential-operator algebra agree
with the actual iterated field derivative (BB (9.9), p. 411). -/
theorem smoothFieldOperator_pow_apply {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω) (n : ℕ) (f : smoothOnFunctions Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) :
    (((smoothFieldOperator Ω V hV) ^ n) f).val x = fieldPower V n f.val x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change (smoothFieldOperator Ω V hV (((smoothFieldOperator Ω V hV) ^ n) f)).val x = _
    rw [smoothFieldOperator_apply Ω V hV _ hx, fieldPower_succ]
    have he : (((smoothFieldOperator Ω V hV) ^ n) f).val =ᶠ[𝓝 x] fieldPower V n f.val := by
      filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
      exact ih hy
    unfold fieldDerivative
    rw [he.fderiv_eq]

end RothschildStein.G3

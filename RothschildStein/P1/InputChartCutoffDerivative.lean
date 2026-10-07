-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.InputBracketApproximation
public import RothschildStein.P1.ReflectedChartTransport
public import RothschildStein.G2.FieldHomogeneity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The input chart cutoff derivative is the
negative reflected model derivative plus the negative full reflected
remainder derivative. This fixes the boundary flux sign. -/
theorem inputChart_fieldDerivative_comp (i : Fin k)
    {ξ η : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U)
    (χ : (Fin (n + m) → ℝ) → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    fieldDerivative (C.Xl i) (fun ζ => χ (C.Θ ζ ξ)) η =
      -fieldDerivative (fun u => C.Y i (-u)) χ (C.Θ η ξ) -
        fieldDerivative (fun u => C.R [i] ξ (-u)) χ (C.Θ η ξ) := by
  have hdΘ := ((C.contDiffOn_Θ_fst hξ).contDiffAt (C.isOpen_U.mem_nhds hη)).differentiableAt
    (by simp)
  have hdχ : DifferentiableAt ℝ χ (C.Θ η ξ) := (hχ.differentiable (by simp)).differentiableAt
  change fderiv ℝ (χ ∘ fun ζ => C.Θ ζ ξ) η (C.Xl i η) = _
  rw [fderiv_comp η hdχ hdΘ, ContinuousLinearMap.comp_apply]
  have ha := C.inputBracket_approx [i] (List.cons_ne_nil i []) hξ hη
  simp only [wordBracket] at ha
  rw [ha, map_sub, map_neg]
  rfl

end RothschildStein.P1.LiftedChart

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.GeneratorTransferCoefficients

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MvPolynomial
open scoped BigOperators
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The complete transfer remainder retains the original chart
remainder, including its lower coordinates, and every reflected input
basis remainder (BB Lemma 11.23, pp. 554–555; low-coordinate repair). -/
def generatorTransferRemainder (i : Fin k) (ξ η u : Fin (n+m) → ℝ) :
    Fin (n+m) → ℝ :=
  C.R [i] η u - ∑ j, eval u (C.generatorTransferCoefficient i j) • C.R (C.B j) ξ (-u)

/-- The generator's output chart direction transfers to the
actual input bracket directions plus the complete remainder. No smaller
coordinate of the original remainder is discarded (BB (11.30)–(11.36)). -/
theorem generator_chart_transfer (i : Fin k)
    {ξ η : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) :
    fderiv ℝ (C.Θ η) ξ (C.Xl i ξ) =
      -(∑ j, eval (C.Θ η ξ) (C.generatorTransferCoefficient i j) •
        fderiv ℝ (fun ζ => C.Θ ζ ξ) η (wordBracket C.Xl (C.B j) η)) +
      C.generatorTransferRemainder i ξ η (C.Θ η ξ) := by
  have ho := C.bracket_approx [i] (by simp) η hη ξ hξ
  simp only [wordBracket] at ho
  rw [ho, C.generator_input_transfer i hξ hη]
  simp only [generatorTransferRemainder]
  abel

/-- Apply the transferred chart direction to any model scalar
kernel. This linear identity precedes integration by parts and the
critical endpoint limit (BB Lemma 11.23, pp. 554–555). -/
theorem generator_model_transfer (i : Fin k) (f : (Fin (n+m) → ℝ) → ℝ)
    {ξ η : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) :
    fderiv ℝ f (C.Θ η ξ) (fderiv ℝ (C.Θ η) ξ (C.Xl i ξ)) =
      -(∑ j, eval (C.Θ η ξ) (C.generatorTransferCoefficient i j) *
        fderiv ℝ f (C.Θ η ξ)
          (fderiv ℝ (fun ζ => C.Θ ζ ξ) η (wordBracket C.Xl (C.B j) η))) +
      fieldDerivative (C.generatorTransferRemainder i ξ η) f (C.Θ η ξ) := by
  rw [C.generator_chart_transfer i hξ hη, map_add, map_neg, map_sum]
  simp only [map_smul, smul_eq_mul, fieldDerivative]

end RothschildStein.P1.LiftedChart

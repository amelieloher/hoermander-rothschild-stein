-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.SpanningLiftStep
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- A finite chain of the actual polynomial one-variable lifting construction. -/
inductive PolynomialLiftChain {a n : ℕ}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) :
    {N : ℕ} → (Fin a → (Fin N → ℝ) → (Fin N → ℝ)) → Prop
  | refl : PolynomialLiftChain X X
  | step {N : ℕ} {Y : Fin a → (Fin N → ℝ) → (Fin N → ℝ)}
      (h : PolynomialLiftChain X Y) (U : Fin a → MvPolynomial (Fin N) ℝ) :
      PolynomialLiftChain X (oneVariableLift Y (fun j x => MvPolynomial.eval x (U j)))

/-- Successive finite polynomial lifting constructions concatenate. -/
theorem PolynomialLiftChain.trans {a n N M : ℕ}
    {X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)}
    {Y : Fin a → (Fin N → ℝ) → (Fin N → ℝ)}
    {Z : Fin a → (Fin M → ℝ) → (Fin M → ℝ)}
    (hXY : PolynomialLiftChain X Y) (hYZ : PolynomialLiftChain Y Z) :
    PolynomialLiftChain X Z := by
  induction hYZ with
  | refl => exact hXY
  | step h U ih => exact .step ih U

/-- A finite chain never removes an original coordinate. -/
theorem PolynomialLiftChain.dimension_le {a n N : ℕ}
    {X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)}
    {Y : Fin a → (Fin N → ℝ) → (Fin N → ℝ)}
    (h : PolynomialLiftChain X Y) : n ≤ N := by
  induction h with
  | refl => exact le_rfl
  | step h U ih => omega
end RothschildStein.L1

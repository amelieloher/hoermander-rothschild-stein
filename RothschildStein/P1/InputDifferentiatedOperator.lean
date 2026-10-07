-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.InputBoundaryMultiplier
public import RothschildStein.P1.TypeKernelInputTranspose

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1.LiftedChart
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- The actual differentiated type operator has
the classified formal-adjoint kernel and the proved critical multiplier. -/
def inputDifferentiatedOperator {lam : ℕ} (hF : C.IsStandardFrame F H K hQ)
    (T : TypeOperator F lam) (i : Fin k) (hw : (w i : ℕ) ≤ lam) :
    TypeOperator F (lam - (w i : ℕ)) :=
  let d := Classical.choice (T.isType 1)
  { kernel := cutoffInputTranspose F (C.Xl i) T.kernel
    isType := C.isTypeKernel_cutoffInputTranspose hF T.isType i hw
    mult := C.typeInputBoundaryMultiplier hF d i
    mult_eq_zero := by
      intro hn
      have hlt : (w i : ℕ) < lam := by omega
      rw [C.typeInputBoundaryMultiplier_eq_zero_of_type_gt hF d i hlt]
      rfl }

end RothschildStein.P1.LiftedChart

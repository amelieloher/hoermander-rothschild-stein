-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.StandardOperatorLinearCombination
public import RothschildStein.P1.TypeKernelInputTranspose

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1.LiftedChart
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- The output differentiated kernel has the
proved lower type. Its multiplier is minus the transpose of the actual
right differentiated operator's multiplier. -/
def outputDifferentiatedOperator {lam : ℕ} (hF : C.IsStandardFrame F H K hQ)
    (T : TypeOperator F lam) (i : Fin k) (hw : (w i : ℕ) ≤ lam)
    (W : TypeOperator F (lam - (w i : ℕ))) : TypeOperator F (lam - (w i : ℕ)) where
  kernel := cutoffOutputDerivative F (C.Xl i) T.kernel
  isType := C.isTypeKernel_cutoffOutputDerivative hF.lifted T.isType i hw
  mult := -W.mult
  mult_eq_zero := by
    intro hn
    have he := W.mult_eq_zero hn
    funext ξ
    change -W.mult ξ = 0
    rw [congrFun he ξ]
    exact neg_zero

/-- The actual output derivative action equals
minus the transposed right action minus the divergence term on V. -/
theorem outputDifferentiatedOperator_apply {lam : ℕ}
    (hF : C.IsStandardFrame F H K hQ) (T : TypeOperator F lam)
    (i : Fin k) (hw : (w i : ℕ) ≤ lam)
    (W : TypeOperator F (lam - (w i : ℕ)))
    (hW : W.kernel = fun ξ η =>
      cutoffInputTranspose F (C.Xl i) (fun x y => T.kernel y x) η ξ)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ))) :
    (C.outputDifferentiatedOperator hF T i hw W).apply φ ξ =
      -W.apply φ ξ - Hormander.Interface.euclideanDivergence (C.Xl i) ξ * T.apply φ ξ := by
  have hn : lam ≠ 0 := by have := (w i).pos; omega
  have hμ (x : Fin (n + m) → ℝ) : T.mult x = 0 := by
    simpa using congrFun (T.mult_eq_zero hn) x
  have hk (x y : Fin (n + m) → ℝ) :
      (C.outputDifferentiatedOperator hF T i hw W).kernel x y =
        (-1 : ℝ) * W.kernel x y +
          (-Hormander.Interface.euclideanDivergence (C.Xl i) x) * T.kernel x y := by
    rw [hW]
    dsimp only [outputDifferentiatedOperator, cutoffInputTranspose]
    ring
  have hm (x : Fin (n + m) → ℝ) :
      (C.outputDifferentiatedOperator hF T i hw W).mult x =
        (-1 : ℝ) * W.mult x + (-Hormander.Interface.euclideanDivergence (C.Xl i) x) * T.mult x := by
    change -W.mult x = _
    rw [hμ]
    ring
  simpa only [neg_one_mul, neg_mul, one_mul, sub_eq_add_neg] using
    C.typeOperator_apply_of_kernel_linear_combination hF
      (C.outputDifferentiatedOperator hF T i hw W) W T (fun _ => -1)
      (fun x => -Hormander.Interface.euclideanDivergence (C.Xl i) x) hk hm φ hξ

end RothschildStein.P1.LiftedChart

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalTransferErrorKernel
public import RothschildStein.P1.RegularKernelFiberDerivative
public import RothschildStein.P1.RegularTranspose
public import RothschildStein.P1.TypeKernelInputMultiplier

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.P1

/-- Input differentiation consumes one regularity
order and preserves global regularity and compact interior support
(BB Theorem 11.24, pp. 555–558). -/
theorem IsRegularKernel.fieldDerivative_input {N b : ℕ} {F : KernelFrame N}
    {r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (hr : IsRegularKernel F (b+1) r)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ))) :
    IsRegularKernel F b (fun ξ η => fieldDerivative Y (fun x => r ξ x) η) :=
  (hr.transpose.fieldDerivative_output Y hY).transpose

namespace LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))

/-- The actual transfer error expression for a
regular kernel includes the input coefficient derivatives and all
input divergences (BB (11.36)–(11.37), pp. 555–556). -/
def regularTransferErrorKernel (i : Fin k)
    (r : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ) (ξ η : Fin (n+m) → ℝ) : ℝ :=
  fieldDerivative (C.Xl i) (fun ζ => r ζ η) ξ +
    (∑ j, fieldDerivative (wordBracket C.Xl (C.B j))
      (fun ζ => C.generatorTransferKernel F i j r ξ ζ) η) +
    ∑ j, Hormander.Interface.euclideanDivergence (wordBracket C.Xl (C.B j)) η *
      C.generatorTransferKernel F i j r ξ η

/-- The regular transfer error consumes only
one regularity order. Its kernel formula is independent of the
regularity budget (BB Theorem 11.24, pp. 555–558). -/
theorem isRegularKernel_regularTransferErrorKernel (hF : C.IsLiftedFrame F)
    {b : ℕ} {r : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ}
    (hr : IsRegularKernel F (b+1) r) (i : Fin k) :
    IsRegularKernel F b (C.regularTransferErrorKernel F i r) := by
  classical
  have hVU : (F.V : Set (Fin (n+m) → ℝ)) ⊆ C.U := subset_closure.trans hF.closure_subset
  have hp (j : Fin (n+m)) : IsRegularKernel F (b+1) (C.generatorTransferKernel F i j r) :=
    C.isRegularKernel_modelMultiplier F hF.Θ_eq hVU hr
      (fun u => MvPolynomial.eval u (C.generatorTransferCoefficient i j)) (G2.contDiff_eval _)
  have hder : IsRegularKernel F b (fun ξ η => ∑ j,
      fieldDerivative (wordBracket C.Xl (C.B j))
        (fun ζ => C.generatorTransferKernel F i j r ξ ζ) η) := by
    apply IsRegularKernel.sum Finset.univ
    intro j _
    exact (hp j).fieldDerivative_input _ (C.transferBasis_smooth F hF j)
  have hdiv : IsRegularKernel F b (fun ξ η => ∑ j,
      Hormander.Interface.euclideanDivergence (wordBracket C.Xl (C.B j)) η *
        C.generatorTransferKernel F i j r ξ η) := by
    apply IsRegularKernel.sum Finset.univ
    intro j _
    have h := (hp j).inputMultiplier (Hormander.Interface.euclideanDivergence (wordBracket C.Xl (C.B j)))
      (contDiffOn_euclideanDivergence F.V _ (C.transferBasis_smooth F hF j))
    have hlow : IsRegularKernel F b (fun ξ η => C.generatorTransferKernel F i j r ξ η *
        Hormander.Interface.euclideanDivergence (wordBracket C.Xl (C.B j)) η) :=
      ⟨h.1.of_le (by simp), h.2⟩
    simpa only [mul_comm] using hlow
  exact ((hr.fieldDerivative_output _ (C.transferGenerator_smooth F hF i)).add hder).add hdiv

end LiftedChart
end RothschildStein.P1

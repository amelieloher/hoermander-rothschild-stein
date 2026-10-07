-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalWeakTransferStandard
public import RothschildStein.P1.TransferActionDecomposition
public import RothschildStein.P1.TransferFiniteSumAlgebra
public import RothschildStein.P1.TransferFilteredSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators
namespace RothschildStein.P1.LiftedChart
open RothschildStein.S
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n+m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- The transfer hypothesis `DerivativeTransfer` holds on
standard frames. Whole-kernel cutoff cancellation proves the endpoint;
the finite decomposition only assembles already proved weak identities
(BB Theorem 11.24, pp. 555–558). -/
theorem derivativeTransfer_standard (hF : C.IsStandardFrame F H K hQ) :
    DerivativeTransfer F w C.Xl C.B := by
  classical
  intro lam T i hw
  refine ⟨C.generatorTransferOperator F hF.lifted T i,
    C.generatorTransferErrorOperator F hF.lifted T i hw, ?_⟩
  intro φ
  have hlam : 1 ≤ lam := (w i).pos.trans_le hw
  let d : TypeDecomposition F lam 1 T.kernel := Classical.choice (T.isType 1)
  let f := fun t : PrincipalTerm F => fun ξ => ∫ η, t.kernel ξ η * φ η
  let b := fun t : PrincipalTerm F => fun j ξ => ∫ η,
    C.generatorTransferKernel F i j t.kernel ξ η *
      fieldDerivative (wordBracket C.Xl (C.B j)) φ η
  let e := fun t : PrincipalTerm F => fun ξ => ∫ η,
    C.principalTransferErrorKernel F hF.lifted t i ξ η * φ η
  let br := fun j ξ => ∫ η, C.generatorTransferKernel F i j d.regular ξ η *
    fieldDerivative (wordBracket C.Xl (C.B j)) φ η
  let er := fun ξ => ∫ η, C.regularTransferErrorKernel F i d.regular ξ η * φ η
  have hp := hasWeakWordDeriv_list_sum C.Xl F.V
    (fun j => C.transferGenerator_smooth F hF.lifted j) [i] d.principal f
    (fun t ξ => (∑ j, b t j ξ) + e t ξ)
    (fun t ht => C.principalTransfer_action_hasWeakWordDeriv_standard hF t i lam hw
      (d.principal_degree t ht) φ)
  have hr := C.regularTransfer_action_hasWeakWordDeriv F hF.lifted d.regular_isRegular i φ
  have hsum := hasWeakWordDeriv_add C.Xl F.V
    (fun j => C.transferGenerator_smooth F hF.lifted j) hp hr
  apply hasWeakWordDeriv_congr_ae C.Xl F.V hsum
  · filter_upwards [ae_restrict_mem F.V.isOpen.measurableSet] with ξ hξ
    exact (C.transfer_originalAction_decomposition hF hlam T d φ hξ).symm
  · filter_upwards [ae_restrict_mem F.V.isOpen.measurableSet] with ξ hξ
    change (d.principal.map (fun t => (∑ j, b t j ξ) + e t ξ)).sum +
      ((∑ j, br j ξ) + er ξ) = _
    rw [transferFiniteSum_reassemble d.principal (fun t j => b t j ξ)
      (fun t => e t ξ) (fun j => br j ξ) (er ξ)]
    have hbasis (j : Fin (n+m)) :
        (d.principal.map (fun t => b t j ξ)).sum + br j ξ =
          (C.generatorTransferOperator F hF.lifted T i j).apply
            (fieldDerivative (wordBracket C.Xl (C.B j)) φ) ξ := by
      let φB := fieldDerivativeTest F.V (wordBracket C.Xl (C.B j))
        (C.transferBasis_smooth F hF.lifted j) φ
      exact (C.transfer_basisAction_decomposition hF T d i hw j φB hξ).symm
    have herror : (d.principal.map (fun t => e t ξ)).sum + er ξ =
        (C.generatorTransferErrorOperator F hF.lifted T i hw).apply φ ξ :=
      (C.transfer_errorAction_decomposition hF T d i hw φ hξ).symm
    rw [add_assoc, herror]
    simp_rw [hbasis]
    rw [C.generatorTransferOperator_sum_eq_filtered F hF.lifted T i hw]

end RothschildStein.P1.LiftedChart

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TransferFiniteRowIntegral
public import RothschildStein.P1.TransferDecompositionKernels
public import RothschildStein.P1.PositiveTypeUniformRadialRows
public import RothschildStein.P1.TransferErrorOperator
public import RothschildStein.P1.StandardFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n+m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- Actual positive-type rows against interior
tests are integrable at every interior output point. -/
theorem positiveTransferRow_integrable (hF : C.IsStandardFrame F H K hQ)
    {lam : ℕ} (hlam : 1 ≤ lam)
    {κ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ} (hκ : IsTypeKernel F lam κ)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) {ξ : Fin (n+m) → ℝ}
    (hξ : ξ ∈ (F.V : Set (Fin (n+m) → ℝ))) :
    Integrable (fun η => κ ξ η * φ η) := by
  have hVU : (F.V : Set (Fin (n+m) → ℝ)) ⊆ C.U := subset_closure.trans hF.lifted.closure_subset
  exact (C.positiveTypeInput_uniformRadialRows hlam hF.lifted hκ H.norm.gauge φ
    isCompact_singleton (singleton_subset_iff.mpr (hVU hξ))).integrable ξ (mem_singleton ξ)

/-- The positive original action equals its
finite principal actions plus its regular action. -/
theorem transfer_originalAction_decomposition (hF : C.IsStandardFrame F H K hQ)
    {lam : ℕ} (hlam : 1 ≤ lam) (T : TypeOperator F lam)
    (d : TypeDecomposition F lam 1 T.kernel)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) {ξ : Fin (n+m) → ℝ}
    (hξ : ξ ∈ (F.V : Set (Fin (n+m) → ℝ))) :
    T.apply φ ξ = (d.principal.map (fun t => ∫ η, t.kernel ξ η * φ η)).sum +
      ∫ η, d.regular ξ η * φ η := by
  let rsTransferOriginalFinNonempty : Nonempty (Fin (n+m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  simp only [TypeOperator.apply, ite_eq_right (show lam ≠ 0 by omega)]
  exact integral_finiteTransferRows F.V d.principal (T.kernel ξ) (fun t => t.kernel ξ)
    (d.regular ξ) ξ φ (fun η _ hne => d.eq_off_diagonal ξ η hne)
    (fun t ht => C.positiveTransferRow_integrable hF hlam
      (t.isTypeKernel lam (d.principal_degree t ht)) φ hξ)
    (d.regular_isRegular.transfer_row_integrable ξ φ)

/-- Each canonical transferred action equals
the corresponding finite principal and regular transferred actions. -/
theorem transfer_basisAction_decomposition (hF : C.IsStandardFrame F H K hQ)
    {lam : ℕ} (T : TypeOperator F lam) (d : TypeDecomposition F lam 1 T.kernel)
    (i : Fin k) (hw : (w i : ℕ) ≤ lam) (j : Fin (n+m))
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) {ξ : Fin (n+m) → ℝ}
    (hξ : ξ ∈ (F.V : Set (Fin (n+m) → ℝ))) :
    (C.generatorTransferOperator F hF.lifted T i j).apply φ ξ =
      (d.principal.map (fun t => ∫ η, C.generatorTransferKernel F i j t.kernel ξ η * φ η)).sum +
      ∫ η, C.generatorTransferKernel F i j d.regular ξ η * φ η := by
  let rsTransferBasisFinNonempty : Nonempty (Fin (n+m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  simp only [TypeOperator.apply, ite_eq_right (C.generatorTransfer_type_pos i j hw).ne',
    generatorTransferOperator]
  have hr := C.isRegularKernel_modelMultiplier F hF.lifted.Θ_eq
    (subset_closure.trans hF.lifted.closure_subset) d.regular_isRegular
    (fun u => MvPolynomial.eval u (C.generatorTransferCoefficient i j)) (G2.contDiff_eval _)
  exact integral_finiteTransferRows F.V d.principal
    (C.generatorTransferKernel F i j T.kernel ξ)
    (fun t => C.generatorTransferKernel F i j t.kernel ξ)
    (C.generatorTransferKernel F i j d.regular ξ) ξ φ
    (fun η _ hne => C.generatorTransferKernel_decomposition F d i j hne)
    (fun t ht => C.positiveTransferRow_integrable hF (C.generatorTransfer_type_pos i j hw)
      (C.isTypeKernel_generatorTransferKernel F hF.lifted
        (t.isTypeKernel lam (d.principal_degree t ht)) i j) φ hξ)
    (hr.transfer_row_integrable ξ φ)

/-- The canonical error action equals the
finite principal errors plus the complete regular error, including
all coefficient derivatives and divergences. -/
theorem transfer_errorAction_decomposition (hF : C.IsStandardFrame F H K hQ)
    {lam : ℕ} (T : TypeOperator F lam) (d : TypeDecomposition F lam 1 T.kernel)
    (i : Fin k) (hw : (w i : ℕ) ≤ lam)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) {ξ : Fin (n+m) → ℝ}
    (hξ : ξ ∈ (F.V : Set (Fin (n+m) → ℝ))) :
    (C.generatorTransferErrorOperator F hF.lifted T i hw).apply φ ξ =
      (d.principal.map (fun t => ∫ η, C.principalTransferErrorKernel F hF.lifted t i ξ η * φ η)).sum +
      ∫ η, C.regularTransferErrorKernel F i d.regular ξ η * φ η := by
  let rsTransferErrorFinNonempty : Nonempty (Fin (n+m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  simp only [TypeOperator.apply, ite_eq_right (generatorTransfer_error_type_pos i hw).ne',
    generatorTransferErrorOperator]
  exact integral_finiteTransferRows F.V d.principal
    (C.cutoffTransferErrorKernel F i T.kernel ξ)
    (fun t => C.principalTransferErrorKernel F hF.lifted t i ξ)
    (C.regularTransferErrorKernel F i d.regular ξ) ξ φ
    (fun η hη hne => C.cutoffTransferErrorKernel_decomposition F hF.lifted d i hξ hη hne)
    (fun t ht => C.positiveTransferRow_integrable hF (generatorTransfer_error_type_pos i hw)
      (C.isTypeKernel_principalTransferErrorKernel F hF.lifted t i lam hw
        (d.principal_degree t ht)) φ hξ)
    ((C.isRegularKernel_regularTransferErrorKernel F hF.lifted d.regular_isRegular i).transfer_row_integrable ξ φ)

end RothschildStein.P1.LiftedChart

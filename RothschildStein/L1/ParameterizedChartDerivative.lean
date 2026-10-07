-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.ChartInverseDerivative
public import RothschildStein.L1.ParameterizedChartInverse

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.L1

/-- The actual shifted inverse has the derivative obtained by
inverting the upper triangular parameter-retaining chart derivative. -/
theorem hasFDerivAt_parameterized_chart_inverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U V : Set (E × F)} (hU : IsOpen U) (hV : IsOpen V)
    (Ψ : E × F → E) (θ : E × F → E) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ U)
    (hinj : ∀ v, InjOn (fun u => Ψ (u, v)) {u | (u, v) ∈ U})
    (hθ : ∀ p ∈ V, (θ p, p.2) ∈ U) (hΨθ : ∀ p ∈ V, Ψ (θ p, p.2) = p.1)
    {p : E × F} (hp : p ∈ V) (L : (E × F) →L[ℝ] E)
    (hL : HasFDerivAt Ψ L (θ p, p.2)) (H : E ≃L[ℝ] E)
    (hH : L.comp (ContinuousLinearMap.inl ℝ E F) = (H : E →L[ℝ] E)) :
    HasFDerivAt θ ((ContinuousLinearMap.fst ℝ E F).comp
      ((upperTriangularDerivativeEquiv H (L.comp (ContinuousLinearMap.inr ℝ E F))).symm :
        (E × F) →L[ℝ] (E × F))) p := by
  have hd : HasFDerivAt (fun q : E × F => (Ψ q, q.2))
      (upperTriangularDerivativeEquiv H (L.comp (ContinuousLinearMap.inr ℝ E F)) :
        (E × F) →L[ℝ] (E × F)) (θ p, p.2) := by
    rw [upperTriangularDerivativeEquiv_eq_prod L H hH]
    exact hL.prodMk hasFDerivAt_snd
  have hh := hasFDerivAt_chart_inverse hU hV (fun q : E × F => (Ψ q, q.2))
    (fun q : E × F => (θ q, q.2)) (hΨ.prodMk contDiffOn_snd)
    (injOn_parameter_retaining_chart Ψ U hinj) hθ
    (fun q hq => Prod.ext (hΨθ q hq) rfl) hp
    (upperTriangularDerivativeEquiv H (L.comp (ContinuousLinearMap.inr ℝ E F))) hd
  exact hh.fst

/-- The horizontal derivative of the shifted inverse is
exactly the inverse horizontal block; the parameter is held fixed. -/
theorem fderiv_parameterized_chart_inverse_inl {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U V : Set (E × F)} (hU : IsOpen U) (hV : IsOpen V)
    (Ψ : E × F → E) (θ : E × F → E) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ U)
    (hinj : ∀ v, InjOn (fun u => Ψ (u, v)) {u | (u, v) ∈ U})
    (hθ : ∀ p ∈ V, (θ p, p.2) ∈ U) (hΨθ : ∀ p ∈ V, Ψ (θ p, p.2) = p.1)
    {p : E × F} (hp : p ∈ V) (L : (E × F) →L[ℝ] E)
    (hL : HasFDerivAt Ψ L (θ p, p.2)) (H : E ≃L[ℝ] E)
    (hH : L.comp (ContinuousLinearMap.inl ℝ E F) = (H : E →L[ℝ] E)) :
    (fderiv ℝ θ p).comp (ContinuousLinearMap.inl ℝ E F) = (H.symm : E →L[ℝ] E) := by
  rw [(hasFDerivAt_parameterized_chart_inverse hU hV Ψ θ hΨ hinj hθ hΨθ hp L hL H hH).fderiv]
  apply ContinuousLinearMap.ext
  intro u
  change ((upperTriangularDerivativeEquiv H
    (L.comp (ContinuousLinearMap.inr ℝ E F))).symm (u, 0)).1 = H.symm u
  rw [upperTriangularDerivativeEquiv_symm_apply]
  simp only [map_zero, sub_zero]

end RothschildStein.L1

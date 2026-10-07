-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FiberDerivativeChain
public import RothschildStein.L1.ProductDerivativeBlocks
public import RothschildStein.L1.ParameterizedChartDerivative
public import RothschildStein.L1.FiberJacobian

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.L1

/-- The actual vertical Jacobian equals the full chart
Jacobian divided by its horizontal Jacobian. The matrix chain and inverse
smoothness are derived from the chart identities (BB pp. 520–521). -/
theorem vertical_jacobian_det_of_fiber_chart {n m : ℕ}
    {U V : Set ((Fin n → ℝ) × (Fin m → ℝ))} (hU : IsOpen U) (hV : IsOpen V)
    (Φ : ((Fin n → ℝ) × (Fin m → ℝ)) → ((Fin n → ℝ) × (Fin m → ℝ)))
    (θ : ((Fin n → ℝ) × (Fin m → ℝ)) → (Fin n → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ U)
    (hinj : ∀ v, InjOn (fun u => (Φ (u, v)).1) {u | (u, v) ∈ U})
    (hmap : ∀ p ∈ V, (θ p, p.2) ∈ U)
    (hbase : ∀ p ∈ V, (Φ (θ p, p.2)).1 = p.1)
    (hderiv : ∀ q ∈ U, ∃ H : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ),
      ((ContinuousLinearMap.fst ℝ _ _).comp (fderiv ℝ Φ q)).comp
        (ContinuousLinearMap.inl ℝ _ _) = (H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
    {p : (Fin n → ℝ) × (Fin m → ℝ)} (hp : p ∈ V) :
    ((fderiv ℝ (fun q : (Fin n → ℝ) × (Fin m → ℝ) => (Φ (θ q, q.2)).2) p).comp
      (ContinuousLinearMap.inr ℝ _ _)).toLinearMap.toMatrix'.det =
      (productDerivativeMatrix (fderiv ℝ Φ (θ p, p.2))).det /
        (((ContinuousLinearMap.fst ℝ _ _).comp (fderiv ℝ Φ (θ p, p.2))).comp
          (ContinuousLinearMap.inl ℝ _ _)).toLinearMap.toMatrix'.det := by
  let Ψ := fun q : (Fin n → ℝ) × (Fin m → ℝ) => (Φ q).1
  have hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ U := hΦ.fst
  have hDΨ (q) (hq : q ∈ U) : fderiv ℝ Ψ q =
      (ContinuousLinearMap.fst ℝ _ _).comp (fderiv ℝ Φ q) :=
    ((hΦ.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt.fst.fderiv
  have hDerΨ : ∀ q ∈ U, ∃ H : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ),
      (fderiv ℝ Ψ q).comp (ContinuousLinearMap.inl ℝ _ _) =
        (H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) := by
    intro q hq
    obtain ⟨H, hH⟩ := hderiv q hq
    refine ⟨H, ?_⟩
    rw [hDΨ q hq]
    exact hH
  have hθ := contDiffOn_parameterized_chart_inverse hU hV Ψ θ hΨ hinj hmap hbase hDerΨ
  obtain ⟨H, hH⟩ := hDerΨ (θ p, p.2) (hmap p hp)
  have hθpartial := fderiv_parameterized_chart_inverse_inl hU hV Ψ θ hΨ hinj hmap hbase hp
    (fderiv ℝ Ψ (θ p, p.2))
    ((hΨ.contDiffAt (hU.mem_nhds (hmap p hp))).differentiableAt (by simp)).hasFDerivAt H hH
  have hc := fiber_parameterization_derivative_chain hU hV Φ θ hΦ hθ hmap hbase hp
  have hm := congrArg productDerivativeMatrix hc
  rw [productDerivativeMatrix_comp, productDerivativeMatrix_parameter_retaining,
    productDerivativeMatrix_base_retaining, hθpartial] at hm
  have hmH : (H.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).toLinearMap.toMatrix' =
      (H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).toLinearMap.toMatrix'⁻¹ :=
    toMatrix_continuousLinearEquiv_symm H
  rw [hmH] at hm
  have hHΦ : ((ContinuousLinearMap.fst ℝ _ _).comp (fderiv ℝ Φ (θ p, p.2))).comp
      (ContinuousLinearMap.inl ℝ _ _) = (H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) := by
    rw [← hDΨ (θ p, p.2) (hmap p hp)]
    exact hH
  rw [hHΦ]
  exact vertical_jacobian_det_of_block_chain _ _ _ _ _ hm

/-- The absolute Jacobian identity preserves both
full and horizontal determinant factors, as required for the lower bound. -/
theorem abs_vertical_jacobian_det_of_fiber_chart {n m : ℕ}
    {U V : Set ((Fin n → ℝ) × (Fin m → ℝ))} (hU : IsOpen U) (hV : IsOpen V)
    (Φ : ((Fin n → ℝ) × (Fin m → ℝ)) → ((Fin n → ℝ) × (Fin m → ℝ)))
    (θ : ((Fin n → ℝ) × (Fin m → ℝ)) → (Fin n → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ U)
    (hinj : ∀ v, InjOn (fun u => (Φ (u, v)).1) {u | (u, v) ∈ U})
    (hmap : ∀ p ∈ V, (θ p, p.2) ∈ U)
    (hbase : ∀ p ∈ V, (Φ (θ p, p.2)).1 = p.1)
    (hderiv : ∀ q ∈ U, ∃ H : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ),
      ((ContinuousLinearMap.fst ℝ _ _).comp (fderiv ℝ Φ q)).comp
        (ContinuousLinearMap.inl ℝ _ _) = (H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
    {p : (Fin n → ℝ) × (Fin m → ℝ)} (hp : p ∈ V) :
    |((fderiv ℝ (fun q : (Fin n → ℝ) × (Fin m → ℝ) => (Φ (θ q, q.2)).2) p).comp
      (ContinuousLinearMap.inr ℝ _ _)).toLinearMap.toMatrix'.det| =
      |(productDerivativeMatrix (fderiv ℝ Φ (θ p, p.2))).det| /
        |(((ContinuousLinearMap.fst ℝ _ _).comp (fderiv ℝ Φ (θ p, p.2))).comp
          (ContinuousLinearMap.inl ℝ _ _)).toLinearMap.toMatrix'.det| := by
  rw [vertical_jacobian_det_of_fiber_chart hU hV Φ θ hΦ hinj hmap hbase hderiv hp, abs_div]

/-- The fiber identity in the actual continuous-linear-map
determinants used for Lebesgue change of variables. -/
theorem abs_vertical_jacobian_linear_det_of_fiber_chart {n m : ℕ}
    {U V : Set ((Fin n → ℝ) × (Fin m → ℝ))} (hU : IsOpen U) (hV : IsOpen V)
    (Φ : ((Fin n → ℝ) × (Fin m → ℝ)) → ((Fin n → ℝ) × (Fin m → ℝ)))
    (θ : ((Fin n → ℝ) × (Fin m → ℝ)) → (Fin n → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ U)
    (hinj : ∀ v, InjOn (fun u => (Φ (u, v)).1) {u | (u, v) ∈ U})
    (hmap : ∀ p ∈ V, (θ p, p.2) ∈ U)
    (hbase : ∀ p ∈ V, (Φ (θ p, p.2)).1 = p.1)
    (hderiv : ∀ q ∈ U, ∃ H : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ),
      ((ContinuousLinearMap.fst ℝ _ _).comp (fderiv ℝ Φ q)).comp
        (ContinuousLinearMap.inl ℝ _ _) = (H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
    {p : (Fin n → ℝ) × (Fin m → ℝ)} (hp : p ∈ V) :
    |((fderiv ℝ (fun q : (Fin n → ℝ) × (Fin m → ℝ) => (Φ (θ q, q.2)).2) p).comp
      (ContinuousLinearMap.inr ℝ _ _)).det| =
      |(fderiv ℝ Φ (θ p, p.2)).det| /
        |(((ContinuousLinearMap.fst ℝ _ _).comp (fderiv ℝ Φ (θ p, p.2))).comp
          (ContinuousLinearMap.inl ℝ _ _)).det| := by
  have hh := abs_vertical_jacobian_det_of_fiber_chart hU hV Φ θ hΦ hinj hmap hbase hderiv hp
  simpa only [LinearMap.det_toMatrix', productDerivativeMatrix_det] using hh

end RothschildStein.L1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FiberJacobianBounds
public import RothschildStein.L1.FiberParameterization
public import RothschildStein.G4.ChartImageVolume

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.L1

/-- Change of variables for the actual vertical fiber map.
Its derivative ratio and injectivity follow from the chart identities
(BB pp. 520–522). Uniform chart domains are supplied separately. -/
theorem fiber_image_volume_bounds {n m : ℕ}
    {U V : Set ((Fin n → ℝ) × (Fin m → ℝ))} (hU : IsOpen U) (hV : IsOpen V)
    (Φ : ((Fin n → ℝ) × (Fin m → ℝ)) → ((Fin n → ℝ) × (Fin m → ℝ)))
    (θ : ((Fin n → ℝ) × (Fin m → ℝ)) → (Fin n → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ U) (hfull : InjOn Φ U)
    (hinj : ∀ v, InjOn (fun u => (Φ (u, v)).1) {u | (u, v) ∈ U})
    (hmap : ∀ p ∈ V, (θ p, p.2) ∈ U)
    (hbase : ∀ p ∈ V, (Φ (θ p, p.2)).1 = p.1)
    (hderiv : ∀ q ∈ U, ∃ H : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ),
      ((ContinuousLinearMap.fst ℝ _ _).comp (fderiv ℝ Φ q)).comp
        (ContinuousLinearMap.inl ℝ _ _) = (H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
    {a b c d : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hAlo : ∀ q ∈ U, a ≤ |(fderiv ℝ Φ q).det|)
    (hAhi : ∀ q ∈ U, |(fderiv ℝ Φ q).det| ≤ b)
    (hHlo : ∀ q ∈ U, c ≤ |(((ContinuousLinearMap.fst ℝ _ _).comp
      (fderiv ℝ Φ q)).comp (ContinuousLinearMap.inl ℝ _ _)).det|)
    (hHhi : ∀ q ∈ U, |(((ContinuousLinearMap.fst ℝ _ _).comp
      (fderiv ℝ Φ q)).comp (ContinuousLinearMap.inl ℝ _ _)).det| ≤ d)
    (y : Fin n → ℝ) {Q : Set (Fin m → ℝ)} (hQ : MeasurableSet Q)
    (hQV : ∀ v ∈ Q, (y, v) ∈ V) :
    ENNReal.ofReal (a / d) * volume Q ≤
        volume ((fun v => (Φ (θ (y, v), v)).2) '' Q) ∧
      volume ((fun v => (Φ (θ (y, v), v)).2) '' Q) ≤
        ENNReal.ofReal (b / c) * volume Q := by
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
  let σ := fun q : (Fin n → ℝ) × (Fin m → ℝ) => (Φ (θ q, q.2)).2
  have hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ V :=
    contDiffOn_fiber_parameterization Φ θ hΦ hθ hmap
  let D := fun v => (fderiv ℝ σ (y, v)).comp (ContinuousLinearMap.inr ℝ _ _)
  have hD : ∀ v ∈ Q, HasFDerivAt (fun v => (Φ (θ (y, v), v)).2) (D v) v := by
    intro v hv
    exact ((hσ.contDiffAt (hV.mem_nhds (hQV v hv))).differentiableAt
      (by simp)).hasFDerivAt.comp v (hasFDerivAt_prodMk_right y v)
  have hbounds : ∀ v ∈ Q, a / d ≤ |(D v).det| ∧ |(D v).det| ≤ b / c := by
    intro v hv
    have hp := hQV v hv
    have hq := hmap (y, v) hp
    exact abs_vertical_jacobian_bounds_of_ratio
      (abs_vertical_jacobian_linear_det_of_fiber_chart hU hV Φ θ hΦ hinj hmap hbase hderiv hp)
      ha hc (hAlo _ hq) (hAhi _ hq) (hHlo _ hq) (hHhi _ hq)
  exact G4.chart_image_volume_bounds hQ _ D hD
    (injOn_fiber_parameterization Φ θ y hfull (fun v hv => hmap _ (hQV v hv))
      (fun v hv => hbase _ (hQV v hv)))
    (fun v hv => (hbounds v hv).1) (fun v hv => (hbounds v hv).2)

end RothschildStein.L1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FiberImageVolume
public import RothschildStein.L1.ParameterizedChartInverseExistence

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.L1

/-- Horizontal coverage constructs one smooth inverse that
works for all measurable parameter slices. The volume estimates use
actual chart derivatives (BB pp. 520–522). -/
theorem exists_fiber_image_volume_bounds {n m : ℕ}
    {U V : Set ((Fin n → ℝ) × (Fin m → ℝ))} (hU : IsOpen U) (hV : IsOpen V)
    (Φ : ((Fin n → ℝ) × (Fin m → ℝ)) → ((Fin n → ℝ) × (Fin m → ℝ)))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ U) (hfull : InjOn Φ U)
    (hinj : ∀ v, InjOn (fun u => (Φ (u, v)).1) {u | (u, v) ∈ U})
    (hcover : ∀ p ∈ V, ∃ u, (u, p.2) ∈ U ∧ (Φ (u, p.2)).1 = p.1)
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
    : ∃ θ : ((Fin n → ℝ) × (Fin m → ℝ)) → (Fin n → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) θ V ∧
      (∀ p ∈ V, (θ p, p.2) ∈ U) ∧
      (∀ p ∈ V, (Φ (θ p, p.2)).1 = p.1) ∧
      ∀ (y : Fin n → ℝ) (Q : Set (Fin m → ℝ)), MeasurableSet Q →
        (∀ v ∈ Q, (y, v) ∈ V) →
        ENNReal.ofReal (a / d) * volume Q ≤
            volume ((fun v => (Φ (θ (y, v), v)).2) '' Q) ∧
          volume ((fun v => (Φ (θ (y, v), v)).2) '' Q) ≤
            ENNReal.ofReal (b / c) * volume Q := by
  let Ψ := fun q : (Fin n → ℝ) × (Fin m → ℝ) => (Φ q).1
  have hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ U := hΦ.fst
  have hDerΨ : ∀ q ∈ U, ∃ H : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ),
      (fderiv ℝ Ψ q).comp (ContinuousLinearMap.inl ℝ _ _) =
        (H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) := by
    intro q hq
    obtain ⟨H, hH⟩ := hderiv q hq
    refine ⟨H, ?_⟩
    have he : fderiv ℝ Ψ q =
        (ContinuousLinearMap.fst ℝ _ _).comp (fderiv ℝ Φ q) :=
      ((hΦ.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt.fst.fderiv
    rw [he]
    exact hH
  obtain ⟨θ, hθ, hmap, hbase⟩ := exists_smooth_parameterized_chart_inverse
    hU hV Ψ hΨ hinj hcover hDerΨ
  refine ⟨θ, hθ, hmap, hbase, ?_⟩
  intro y Q hQ hQV
  exact fiber_image_volume_bounds hU hV Φ θ hΦ hfull hinj hmap hbase hderiv
    ha hc hAlo hAhi hHlo hHhi y hQ hQV

end RothschildStein.L1

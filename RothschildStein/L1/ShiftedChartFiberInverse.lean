-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FiberImageVolumeExistence
public import RothschildStein.L1.HorizontalChartInvertibility

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.L1

/-- Full lifted chart data and the projected shifted horizontal
chart construct the joint inverse and both fiber-image volume bounds.
The horizontal equivalences are derived from actual Jacobian bounds,
not supplied as an independent inverse premise (BB pp. 520–522). -/
theorem exists_fiber_inverse_bounds_of_shifted_chart_data {n m : ℕ}
    {U W : Set (Fin n → ℝ)} {V : Set (Fin m → ℝ)}
    (hU : IsOpen U) (hW : IsOpen W) (hV : IsOpen V)
    (Φ : ((Fin n → ℝ) × (Fin m → ℝ)) → ((Fin n → ℝ) × (Fin m → ℝ)))
    (Ψ : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ V)) (hfull : InjOn Φ (U ×ˢ V))
    (hproj : ∀ u ∈ U, ∀ v ∈ V, (Φ (u,v)).1 = Ψ u v)
    (hinj : ∀ v ∈ V, InjOn (fun u => Ψ u v) U)
    (hcover : ∀ y ∈ W, ∀ v ∈ V, ∃ u ∈ U, Ψ u v = y)
    {a b c d : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hAlo : ∀ q ∈ U ×ˢ V, a ≤ |(fderiv ℝ Φ q).det|)
    (hAhi : ∀ q ∈ U ×ˢ V, |(fderiv ℝ Φ q).det| ≤ b)
    (hHlo : ∀ u ∈ U, ∀ v ∈ V, c ≤ |(fderiv ℝ (fun y => Ψ y v) u).det|)
    (hHhi : ∀ u ∈ U, ∀ v ∈ V, |(fderiv ℝ (fun y => Ψ y v) u).det| ≤ d) :
    ∃ θ : ((Fin n → ℝ) × (Fin m → ℝ)) → (Fin n → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) θ (W ×ˢ V) ∧
      (∀ p ∈ W ×ˢ V, (θ p,p.2) ∈ U ×ˢ V) ∧
      (∀ p ∈ W ×ˢ V, (Φ (θ p,p.2)).1 = p.1) ∧
      ∀ y ∈ W, ∀ Q : Set (Fin m → ℝ), MeasurableSet Q → Q ⊆ V →
        ENNReal.ofReal (a/d) * volume Q ≤
          volume ((fun v => (Φ (θ (y,v),v)).2) '' Q) ∧
        volume ((fun v => (Φ (θ (y,v),v)).2) '' Q) ≤
          ENNReal.ofReal (b/c) * volume Q := by
  have hd : ∀ q ∈ U ×ˢ V,
      ((ContinuousLinearMap.fst ℝ _ _).comp (fderiv ℝ Φ q)).comp
        (ContinuousLinearMap.inl ℝ _ _) = fderiv ℝ (fun y => Ψ y q.2) q.1 := by
    intro q hq
    exact horizontal_derivative_eq_of_projection hU Φ Ψ hproj hq.1 hq.2
      ((hΦ.contDiffAt ((hU.prod hV).mem_nhds hq)).differentiableAt (by simp))
  have hderiv : ∀ q ∈ U ×ˢ V, ∃ H : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ),
      ((ContinuousLinearMap.fst ℝ _ _).comp (fderiv ℝ Φ q)).comp
        (ContinuousLinearMap.inl ℝ _ _) = (H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) := by
    intro q hq
    rw [hd q hq]
    exact exists_continuousLinearEquiv_of_det_ne_zero _
      (abs_pos.mp (hc.trans_le (hHlo q.1 hq.1 q.2 hq.2)))
  have hi : ∀ v, InjOn (fun u => (Φ (u,v)).1) {u | (u,v) ∈ U ×ˢ V} := by
    intro v u hu u' hu' he
    apply hinj v hu.2 hu.1 hu'.1
    change Ψ u v = Ψ u' v
    rw [← hproj u hu.1 v hu.2, ← hproj u' hu'.1 v hu'.2]
    exact he
  have hcov : ∀ p ∈ W ×ˢ V, ∃ u, (u,p.2) ∈ U ×ˢ V ∧ (Φ (u,p.2)).1 = p.1 := by
    intro p hp
    obtain ⟨u,hu,he⟩ := hcover p.1 hp.1 p.2 hp.2
    exact ⟨u,⟨hu,hp.2⟩,(hproj u hu p.2 hp.2).trans he⟩
  obtain ⟨θ,hθ,hm,hbase,hbounds⟩ := exists_fiber_image_volume_bounds
    (hU.prod hV) (hW.prod hV) Φ hΦ hfull hi hcov hderiv ha hc hAlo hAhi
    (fun q hq => by rw [hd q hq]; exact hHlo q.1 hq.1 q.2 hq.2)
    (fun q hq => by rw [hd q hq]; exact hHhi q.1 hq.1 q.2 hq.2)
  exact ⟨θ,hθ,hm,hbase,fun y hy Q hQ hQV => hbounds y Q hQ (fun v hv => ⟨hy,hQV hv⟩)⟩

end RothschildStein.L1

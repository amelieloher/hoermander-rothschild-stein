-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.ShiftedChartFiberInverse
public import RothschildStein.L1.FiberChartVolumeBounds
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.L1

/-- Actual projected slice data and chart containments imply
both fiber bounds, constructing the joint inverse rather than assuming
it. The containments are explicit geometric inputs (BB pp. 520–522). -/
theorem fiberVolume_bounds_of_shifted_chart_data {n m : ℕ}
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
    (hHhi : ∀ u ∈ U, ∀ v ∈ V, |(fderiv ℝ (fun y => Ψ y v) u).det| ≤ d)
    {Q : Set (Fin m → ℝ)} (hQ : MeasurableSet Q) (hQV : Q ⊆ V)
    {Small Large : Set (Fin (n+m) → ℝ)}
    (hsmall : Small ⊆ (fun q => joinPoint (Φ q).1 (Φ q).2) '' (U ×ˢ Q))
    (hlarge : (fun q => joinPoint (Φ q).1 (Φ q).2) '' (U ×ˢ Q) ⊆ Large) :
    ∀ y ∈ W, ENNReal.ofReal (a/d) * volume Q ≤ fiberVolume Large y ∧
      fiberVolume Small y ≤ ENNReal.ofReal (b/c) * volume Q := by
  obtain ⟨θ,_hθ,hmap,hbase,hbounds⟩ := exists_fiber_inverse_bounds_of_shifted_chart_data
    hU hW hV Φ Ψ hΦ hfull hproj hinj hcover ha hc hAlo hAhi hHlo hHhi
  have hi : ∀ v, InjOn (fun u => (Φ (u,v)).1) {u | (u,v) ∈ U ×ˢ V} := by
    intro v u hu u' hu' he
    apply hinj v hu.2 hu.1 hu'.1
    change Ψ u v = Ψ u' v
    rw [← hproj u hu.1 v hu.2, ← hproj u' hu'.1 v hu'.2]
    exact he
  intro y hy
  have hb := hbounds y hy Q hQ hQV
  have he := fiberVolume_parameterized_chart Φ θ y hi
    (fun v hv => hmap (y,v) ⟨hy,hQV hv⟩)
    (fun v hv => hbase (y,v) ⟨hy,hQV hv⟩)
  have hset : (U ×ˢ V) ∩ Prod.snd ⁻¹' Q = U ×ˢ Q := by
    ext p
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,hQV h.2⟩,h.2⟩⟩
  rw [← he,hset] at hb
  exact ⟨hb.1.trans (fiberVolume_mono hlarge y),
    (fiberVolume_mono hsmall y).trans hb.2⟩

end RothschildStein.L1

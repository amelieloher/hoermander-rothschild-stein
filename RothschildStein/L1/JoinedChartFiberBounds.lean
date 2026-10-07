-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.ShiftedChartFiberBounds
public import RothschildStein.L1.ChartJacobianCarrierTransfer
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.L1

/-- A joined-coordinate lifted chart and the actual shifted
original chart imply fiber bounds. Product smoothness, injectivity and
the full product Jacobian are derived by coordinate conjugation
(BB pp. 520–522, (10.49)). -/
theorem fiberVolume_bounds_of_joined_chart_data {n m : ℕ}
    {D : Set (Fin (n+m) → ℝ)} {U W : Set (Fin n → ℝ)} {V : Set (Fin m → ℝ)}
    (hD : IsOpen D) (hU : IsOpen U) (hW : IsOpen W) (hV : IsOpen V)
    (F : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ))
    (Ψ : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → ℝ))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F D) (hfull : InjOn F D)
    (hmixed : ∀ u ∈ U, ∀ v ∈ V, joinPoint u v ∈ D)
    (hproj : ∀ u ∈ U, ∀ v ∈ V, basePoint (F (joinPoint u v)) = Ψ u v)
    (hinj : ∀ v ∈ V, InjOn (fun u => Ψ u v) U)
    (hcover : ∀ y ∈ W, ∀ v ∈ V, ∃ u ∈ U, Ψ u v = y)
    {a b c d : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hAlo : ∀ p ∈ D, a ≤ |(fderiv ℝ F p).det|)
    (hAhi : ∀ p ∈ D, |(fderiv ℝ F p).det| ≤ b)
    (hHlo : ∀ u ∈ U, ∀ v ∈ V, c ≤ |(fderiv ℝ (fun y => Ψ y v) u).det|)
    (hHhi : ∀ u ∈ U, ∀ v ∈ V, |(fderiv ℝ (fun y => Ψ y v) u).det| ≤ d)
    {Q : Set (Fin m → ℝ)} (hQ : MeasurableSet Q) (hQV : Q ⊆ V)
    {Small Large : Set (Fin (n+m) → ℝ)}
    (hsmall : Small ⊆ (fun p => F (joinPoint p.1 p.2)) '' (U ×ˢ Q))
    (hlarge : (fun p => F (joinPoint p.1 p.2)) '' (U ×ˢ Q) ⊆ Large) :
    ∀ y ∈ W, ENNReal.ofReal (a/d) * volume Q ≤ fiberVolume Large y ∧
      fiberVolume Small y ≤ ENNReal.ofReal (b/c) * volume Q := by
  let e := P1.paddingCoordinates n m
  let Φ := fun p => e (F (e.symm p))
  have he : ∀ p : (Fin n → ℝ) × (Fin m → ℝ), e.symm p = joinPoint p.1 p.2 := by
    intro p
    exact P1.paddingJoinCLM_apply n m p.1 p.2
  have hmap : MapsTo e.symm (U ×ˢ V) D := fun p hp => by
    rw [he p]
    exact hmixed p.1 hp.1 p.2 hp.2
  have hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ V) :=
    e.contDiff.comp_contDiffOn (hF.comp e.symm.contDiff.contDiffOn hmap)
  have hi : InjOn Φ (U ×ˢ V) := by
    intro p hp p' hp' hh
    exact e.symm.injective (hfull (hmap hp) (hmap hp') (e.injective hh))
  have hpr : ∀ u ∈ U, ∀ v ∈ V, (Φ (u,v)).1 = Ψ u v := by
    intro u hu v hv
    change basePoint (F (e.symm (u,v))) = Ψ u v
    rw [he (u,v)]
    exact hproj u hu v hv
  have hdet : ∀ p ∈ U ×ˢ V, |(fderiv ℝ Φ p).det| = |(fderiv ℝ F (e.symm p)).det| := by
    intro p hp
    exact abs_det_fderiv_padding_chart F p
      ((hF.contDiffAt (hD.mem_nhds (hmap hp))).differentiableAt (by simp))
  have hj : (fun p => joinPoint (Φ p).1 (Φ p).2) =
      (fun p => F (joinPoint p.1 p.2)) := by
    funext p
    change joinPoint (P1.paddingBaseCLM n m (F (e.symm p)))
      (P1.paddingFiberCLM n m (F (e.symm p))) = F (joinPoint p.1 p.2)
    rw [← P1.paddingJoinCLM_apply,P1.paddingJoinCLM_projections,he p]
  apply fiberVolume_bounds_of_shifted_chart_data hU hW hV Φ Ψ hΦ hi hpr hinj hcover ha hc
    (fun p hp => by rw [hdet p hp]; exact hAlo _ (hmap hp))
    (fun p hp => by rw [hdet p hp]; exact hAhi _ (hmap hp))
    hHlo hHhi hQ hQV
  · simpa only [hj] using hsmall
  · simpa only [hj] using hlarge

end RothschildStein.L1

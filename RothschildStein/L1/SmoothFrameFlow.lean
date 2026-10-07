-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FrameCoefficientDerivative
public import Mathlib.Analysis.Calculus.MeanValue
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1

/-- The actual constant-coefficient frame combination has a jointly
smooth parameter flow, and zero coefficients give the identity for every
time on its cylinder (BB (10.15), p. 499; Proposition 10.29, p. 509). -/
theorem exists_smooth_frame_parameter_flow {d N : ℕ}
    (Ω : Set (Fin N → ℝ)) (hΩ : IsOpen Ω)
    (Y : Fin d → (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    (x : Fin N → ℝ) (hx : x ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ ∃ τ : ℝ, 0 < τ ∧
      ∃ Φ : (((Fin d → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ),
        ball (0,x) r ⊆ (univ : Set (Fin d → ℝ)) ×ˢ Ω ∧
        ContDiffOn ℝ (⊤ : ℕ∞) Φ (ball (0,x) r ×ˢ Ioo (-τ) τ) ∧
        (∀ q ∈ ball (0,x) r, Φ (q,0) = q.2 ∧
          ∀ t ∈ Ioo (-τ) τ, Φ (q,t) ∈ Ω ∧
            HasDerivAt (fun s => Φ (q,s)) (frameCoefficientField Y (q.1,Φ (q,t))) t) ∧
        ∀ y ∈ ball x r, ∀ t ∈ Ioo (-τ) τ, Φ ((0,y),t) = y := by
  obtain ⟨r,hr,τ,hτ,Φ,hball,hΦ,hsol⟩ := G1.exists_contDiff_parameter_flow
    (n := (⊤ : ℕ∞)) (by simp) isOpen_univ hΩ (frameCoefficientField Y)
    (frameCoefficientField_contDiffOn Y hY) (mem_univ (0 : Fin d → ℝ)) hx
  refine ⟨r,hr,τ,hτ,Φ,hball,hΦ,hsol,?_⟩
  intro y hy t ht
  have hp : ((0 : Fin d → ℝ),y) ∈ ball (0,x) r := by
    simpa only [Metric.mem_ball,Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : 0 ≤ dist y x)] using hy
  have hder : ∀ s ∈ Ioo (-τ) τ, HasDerivAt (fun v => Φ ((0,y),v)) 0 s := by
    intro s hs
    simpa only [frameCoefficientField_zero] using ((hsol (0,y) hp).2 s hs).2
  have ht0 : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith,hτ⟩
  have he := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun s hs => (hder s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hder s hs).deriv) ht ht0
  exact he.trans (hsol (0,y) hp).1
end RothschildStein.L1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FrameFlowReversal
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.L1

/-- Scaling the constant coefficient vector is actual time
rescaling, on every interval where both trajectories are defined. -/
theorem frameFlow_smul_coefficients {d N : ℕ}
    {Ω : Set (Fin N → ℝ)} {U : Set ((Fin d → ℝ) × (Fin N → ℝ))}
    (hΩ : IsOpen Ω) {τ b : ℝ} (hb : 0 < b) (hbτ : b ≤ τ)
    (Y : Fin d → (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    (Φ : (((Fin d → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hsol : ∀ q ∈ U, Φ (q,0) = q.2 ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s => Φ (q,s)) (frameCoefficientField Y (q.1,Φ (q,t))) t ∧
      Φ (q,t) ∈ Ω)
    (u : Fin d → ℝ) (x : Fin N → ℝ) (s : ℝ)
    (hp : (u,x) ∈ U) (hs : (s • u,x) ∈ U)
    (hst : ∀ v ∈ Ioo (-b) b, s*v ∈ Ioo (-τ) τ)
    {t : ℝ} (ht : t ∈ Ioo (-b) b) :
    Φ ((s • u,x),t) = Φ ((u,x),s*t) := by
  have hz : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => frameCoefficientField Y (s • u,y)) Ω :=
    (frameCoefficientField_contDiffOn Y hY).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨mem_univ _,hy⟩)
  have hsub : Ioo (-b) b ⊆ Ioo (-τ) τ := by
    intro v hv
    exact ⟨by linarith [hv.1],by linarith [hv.2]⟩
  have he := G1.integralCurve_eqOn hΩ hz
    (show (0 : ℝ) ∈ Ioo (-b) b from ⟨by linarith,hb⟩)
    (α := fun v => Φ ((s • u,x),v)) (β := fun v => Φ ((u,x),s*v))
    (fun v hv => (hsol (s • u,x) hs).2 v (hsub hv))
    (fun v hv => by
      refine ⟨?_,((hsol (u,x) hp).2 (s*v) (hst v hv)).2⟩
      simpa only [Function.comp_def,one_mul,mul_one,← frameCoefficientField_smul] using
        (((hsol (u,x) hp).2 (s*v) (hst v hv)).1.scomp v
          ((hasDerivAt_id v).const_mul s)))
    (by simp only [mul_zero,(hsol (s • u,x) hs).1,(hsol (u,x) hp).1])
  exact he ht
end RothschildStein.L1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FrameCoefficientFields
public import RothschildStein.G1.FlowComposition
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.L1

/-- The parameter field is linear in its constant coefficients. -/
theorem frameCoefficientField_smul {d N : ℕ}
    (Y : Fin d → (Fin N → ℝ) → (Fin N → ℝ))
    (a : ℝ) (u : Fin d → ℝ) (x : Fin N → ℝ) :
    frameCoefficientField Y (a • u,x) = a • frameCoefficientField Y (u,x) := by
  rw [← frameValueCLM_apply,← frameValueCLM_apply,map_smul]

/-- Negating the actual coefficient vector reverses the actual
frame flow on its common time interval. -/
theorem frameFlow_neg_coefficients {d N : ℕ}
    {Ω : Set (Fin N → ℝ)} {U : Set ((Fin d → ℝ) × (Fin N → ℝ))}
    (hΩ : IsOpen Ω) {τ : ℝ} (hτ : 0 < τ)
    (Y : Fin d → (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    (Φ : (((Fin d → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hsol : ∀ q ∈ U, Φ (q,0) = q.2 ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s => Φ (q,s)) (frameCoefficientField Y (q.1,Φ (q,t))) t ∧
      Φ (q,t) ∈ Ω)
    (u : Fin d → ℝ) (x : Fin N → ℝ)
    (hp : (u,x) ∈ U) (hn : (-u,x) ∈ U) {t : ℝ} (ht : t ∈ Ioo (-τ) τ) :
    Φ ((-u,x),t) = Φ ((u,x),-t) := by
  have hz : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => frameCoefficientField Y (-u,y)) Ω :=
    (frameCoefficientField_contDiffOn Y hY).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨mem_univ _,hy⟩)
  have hneg : ∀ y, frameCoefficientField Y (-u,y) = -frameCoefficientField Y (u,y) := by
    intro y
    rw [← neg_one_smul ℝ u,frameCoefficientField_smul,neg_one_smul]
  have he := G1.integralCurve_eqOn hΩ hz
    (show (0 : ℝ) ∈ Ioo (-τ) τ from ⟨by linarith,hτ⟩)
    (α := fun s => Φ ((-u,x),s)) (β := fun s => Φ ((u,x),-s))
    (fun s hs => (hsol (-u,x) hn).2 s hs)
    (fun s hs => by
      have hs' : -s ∈ Ioo (-τ) τ := ⟨by linarith [hs.2],by linarith [hs.1]⟩
      refine ⟨?_,((hsol (u,x) hp).2 (-s) hs').2⟩
      simpa only [Function.comp_def,neg_one_smul,← hneg] using
        (((hsol (u,x) hp).2 (-s) hs').1.scomp s (hasDerivAt_id s).neg))
    (by simp only [neg_zero,(hsol (-u,x) hn).1,(hsol (u,x) hp).1])
  exact he ht
/-- Actual canonical flow endpoints reverse when both endpoint
coefficient pairs stay in the flow's initial-point domain. -/
theorem frameFlow_reverse_endpoint {d N : ℕ}
    {Ω : Set (Fin N → ℝ)} {U : Set ((Fin d → ℝ) × (Fin N → ℝ))}
    (hΩ : IsOpen Ω) {τ : ℝ} (hτ : 0 < τ)
    (Y : Fin d → (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    (Φ : (((Fin d → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hsol : ∀ q ∈ U, Φ (q,0) = q.2 ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s => Φ (q,s)) (frameCoefficientField Y (q.1,Φ (q,t))) t ∧
      Φ (q,t) ∈ Ω)
    (u : Fin d → ℝ) (x : Fin N → ℝ) (hp : (u,x) ∈ U)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (he : (u,Φ ((u,x),t)) ∈ U) (hne : (-u,Φ ((u,x),t)) ∈ U) :
    Φ ((-u,Φ ((u,x),t)),t) = x := by
  rw [frameFlow_neg_coefficients hΩ hτ Y hY Φ hsol u _ he hne ht]
  have hz : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => frameCoefficientField Y (u,y)) Ω :=
    (frameCoefficientField_contDiffOn Y hY).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨mem_univ _,hy⟩)
  exact G1.localFlow_inverse (U := {y | (u,y) ∈ U}) hΩ hz hτ
    (fun q => Φ ((u,q.1),q.2)) (fun y hy => hsol (u,y) hy) hp ht he
end RothschildStein.L1

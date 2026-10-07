-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.VariationOfConstants
public import RothschildStein.G4.InverseFundamentalDerivative
public import RothschildStein.G4.FlowTransitionDerivative
public import RothschildStein.G1.ParameterJetBounds
public import RothschildStein.G1.SmoothDependenceMain

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory

namespace RothschildStein.G4

/-- The remaining time t-s stays in the same oriented zero-to-t
interval, so transition flow times require no larger time domain
(BB Lemma 9.48, pp. 441–442). -/
theorem sub_mem_uIcc_zero {s t : ℝ} (hs : s ∈ uIcc 0 t) : t - s ∈ uIcc 0 t := by
  rcases le_total 0 t with h | h
  · rw [uIcc_of_le h] at hs ⊢
    constructor <;> linarith [hs.1, hs.2]
  · rw [uIcc_of_ge h] at hs ⊢
    constructor <;> linarith [hs.1, hs.2]

/-- An actual inhomogeneous variational solution has the actual
flow-transition integral formula. Every intermediate flow endpoint must
remain in the local initial-point domain; no invariant domain is assumed
(BB Lemma 9.48, pp. 441–442). -/
theorem localFlow_variation_integral_of_joint_contDiff
    {N : ℕ} {Ω U : Set (Fin N → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {W : (Fin N → ℝ) → (Fin N → ℝ)} (hW : ContDiffOn ℝ (⊤ : ℕ∞) W Ω)
    {τ : ℝ} (hτ : 0 < τ) (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ s ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x, v)) (W (Φ (x, s))) s ∧ Φ (x, s) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hend : ∀ s ∈ uIcc 0 t, Φ (x, s) ∈ U)
    (F v : ℝ → Fin N → ℝ) (hF : ContinuousOn F (uIcc 0 t))
    (hv : ∀ s ∈ uIcc 0 t,
      HasDerivAt v (fderiv ℝ W (Φ (x, s)) (v s) + F s) s) (hzero : v 0 = 0) :
    v t = ∫ s in 0..t, fderiv ℝ (fun y => Φ (y, t - s)) (Φ (x, s)) (F s) := by
  let A := fun s => fderiv ℝ (fun y => Φ (y, -s)) (Φ (x, s))
  let D := fun s => fderiv ℝ W (Φ (x, s))
  let J := fderiv ℝ (fun y => Φ (y, t)) x
  let T := fun s => fderiv ℝ (fun y => Φ (y, t - s)) (Φ (x, s))
  have ht₀ : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
  have hsub : uIcc 0 t ⊆ Ioo (-τ) τ := ordConnected_Ioo.uIcc_subset ht₀ ht
  have hA : ∀ s ∈ uIcc 0 t, HasDerivAt A (-(A s).comp (D s)) s := fun s hs =>
    localFlow_opposite_jacobian_hasDerivAt_of_joint_contDiff hΩ hU hW hτ Φ hjoint hΦ hx
      (hsub hs) (hend s hs)
  have hpoint := RothschildStein.G1.localFlow_inverse hΩ hW hτ Φ hΦ hx ht (hend t (right_mem_uIcc))
  have hneg : -t ∈ Ioo (-τ) τ := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hinv := RothschildStein.G1.localFlow_inverse_fderiv_of_joint_contDiff hΩ hU hW hτ
    Φ hjoint hΦ (hend t right_mem_uIcc) hneg (by rw [hpoint]; exact hx)
  rw [neg_neg, hpoint] at hinv
  have htransition : ∀ s ∈ uIcc 0 t, J.comp (A s) = T s := fun s hs =>
    localFlow_transition_inverse_fderiv_of_joint_contDiff hΩ hU hW hτ Φ hjoint hΦ hx
      (hsub hs) ht (hsub (sub_mem_uIcc_zero hs)) (hend s hs)
  exact transported_variation_of_constants A D T F v J t hA hv hF hzero hinv htransition

end RothschildStein.G4

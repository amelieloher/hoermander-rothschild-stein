-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.FlowJacobianInverse

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G4

/-- Differentiating the actual flow composition identifies its
transition Jacobian on the finite time/domain overlap
(BB Lemma 9.48, pp. 441–442). -/
theorem localFlow_transition_fderiv_of_joint_contDiff
    {N : ℕ} {Ω U : Set (Fin N → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {Z : (Fin N → ℝ) → (Fin N → ℝ)} (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω)
    {τ : ℝ} (hτ : 0 < τ) (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) {s t : ℝ}
    (hs : s ∈ Ioo (-τ) τ) (ht : t ∈ Ioo (-τ) τ)
    (hts : t - s ∈ Ioo (-τ) τ) (hend : Φ (x, s) ∈ U) :
    (fderiv ℝ (fun y => Φ (y, t - s)) (Φ (x, s))).comp
      (fderiv ℝ (fun y => Φ (y, s)) x) = fderiv ℝ (fun y => Φ (y, t)) x := by
  have hsp : ∀ y ∈ U, ∀ v ∈ Ioo (-τ) τ,
      DifferentiableAt ℝ (fun z => Φ (z, v)) y := by
    intro y hy v hv
    exact ((hjoint.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hy, hv⟩)).comp y
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have heq : (fun y => Φ (Φ (y, s), t - s)) =ᶠ[𝓝 x] (fun y => Φ (y, t)) := by
    filter_upwards [hU.mem_nhds hx,
      (hsp x hx s hs).continuousAt.preimage_mem_nhds (hU.mem_nhds hend)] with y hy hys
    simpa only [sub_add_cancel] using RothschildStein.G1.localFlow_composition hΩ hZ hτ Φ hΦ
      hy hs hts (by simpa only [sub_add_cancel] using ht) hys
  have hc := (hsp _ hend (t - s) hts).hasFDerivAt.comp x (hsp x hx s hs).hasFDerivAt
  exact (hc.congr_of_eventuallyEq heq.symm).unique (hsp x hx t ht).hasFDerivAt

/-- The forward endpoint Jacobian composed with the opposite-time
Jacobian is exactly the actual transition Jacobian, on its stated overlap
(BB Lemma 9.48, pp. 441–442). -/
theorem localFlow_transition_inverse_fderiv_of_joint_contDiff
    {N : ℕ} {Ω U : Set (Fin N → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {Z : (Fin N → ℝ) → (Fin N → ℝ)} (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω)
    {τ : ℝ} (hτ : 0 < τ) (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) {s t : ℝ}
    (hs : s ∈ Ioo (-τ) τ) (ht : t ∈ Ioo (-τ) τ)
    (hts : t - s ∈ Ioo (-τ) τ) (hend : Φ (x, s) ∈ U) :
    (fderiv ℝ (fun y => Φ (y, t)) x).comp
      (fderiv ℝ (fun y => Φ (y, -s)) (Φ (x, s))) =
        fderiv ℝ (fun y => Φ (y, t - s)) (Φ (x, s)) := by
  have hneg : -s ∈ Ioo (-τ) τ := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hpoint := RothschildStein.G1.localFlow_inverse hΩ hZ hτ Φ hΦ hx hs hend
  have hi := RothschildStein.G1.localFlow_inverse_fderiv_of_joint_contDiff hΩ hU hZ hτ
    Φ hjoint hΦ hend hneg (by rw [hpoint]; exact hx)
  rw [neg_neg, hpoint] at hi
  have htder := localFlow_transition_fderiv_of_joint_contDiff hΩ hU hZ hτ Φ hjoint hΦ hx hs ht hts hend
  have h := congrArg (fun L : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) =>
    L.comp (fderiv ℝ (fun y => Φ (y, -s)) (Φ (x, s)))) htder
  rw [ContinuousLinearMap.comp_assoc, hi, ContinuousLinearMap.comp_id] at h
  exact h.symm

end RothschildStein.G4

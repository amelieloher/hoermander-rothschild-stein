-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.FlowComposition
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

/-- Under joint smoothness of the local flow, opposite-time
spatial derivatives compose to the identity (BB Prop 1.2, p. 3). -/
theorem localFlow_inverse_fderiv_of_joint_contDiff {N : ℕ} {Ω U : Set (Fin N → ℝ)}
    (hΩ : IsOpen Ω) (hU : IsOpen U) {Z : (Fin N → ℝ) → (Fin N → ℝ)}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (htx : Φ (x, t) ∈ U) :
    (fderiv ℝ (fun y => Φ (y, -t)) (Φ (x, t))).comp
      (fderiv ℝ (fun y => Φ (y, t)) x) = ContinuousLinearMap.id ℝ (Fin N → ℝ) := by
  have hneg : -t ∈ Ioo (-τ) τ := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hsmooth : ∀ y ∈ U, ∀ v ∈ Ioo (-τ) τ,
      ContDiffAt ℝ (⊤ : ℕ∞) (fun z => Φ (z, v)) y := by
    intro y hy v hv
    exact (hjoint.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hy, hv⟩)).comp y
      (contDiffAt_id.prodMk contDiffAt_const)
  have hforward := (hsmooth x hx t ht).differentiableAt (by simp)
  have hinverse := (hsmooth _ htx (-t) hneg).differentiableAt (by simp)
  have heq : (fun y => Φ (Φ (y, t), -t)) =ᶠ[𝓝 x] id := by
    filter_upwards [hU.mem_nhds hx,
      hforward.continuousAt.preimage_mem_nhds (hU.mem_nhds htx)] with y hy hyt
    exact localFlow_inverse hΩ hZ hτ Φ hΦ hy ht hyt
  have hcomp := hinverse.hasFDerivAt.comp x hforward.hasFDerivAt
  have hid := hcomp.congr_of_eventuallyEq heq.symm
  exact hid.unique (hasFDerivAt_id x)

/-- Under joint smoothness: the Jacobian determinant is
nonzero. This is weaker than the still-unproved positive Liouville formula
(BB Prop 1.2, p. 3). -/
theorem localFlow_jacobian_ne_zero_of_joint_contDiff {N : ℕ}
    {Ω U : Set (Fin N → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {Z : (Fin N → ℝ) → (Fin N → ℝ)}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (htx : Φ (x, t) ∈ U) :
    LinearMap.det (fderiv ℝ (fun y => Φ (y, t)) x).toLinearMap ≠ 0 := by
  have heq := localFlow_inverse_fderiv_of_joint_contDiff hΩ hU hZ hτ Φ hjoint hΦ hx ht htx
  have hdet := congrArg (fun L : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) =>
    LinearMap.det L.toLinearMap) heq
  change LinearMap.det ((fderiv ℝ (fun y => Φ (y, -t)) (Φ (x, t))).toLinearMap.comp
    (fderiv ℝ (fun y => Φ (y, t)) x).toLinearMap) = LinearMap.det LinearMap.id at hdet
  rw [LinearMap.det_comp, LinearMap.det_id] at hdet
  intro hz
  rw [hz, mul_zero] at hdet
  exact zero_ne_one hdet

end RothschildStein.G1

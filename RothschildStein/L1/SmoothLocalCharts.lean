-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RightInverseLocalChart
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.L1

/-- Smoothness and invertible derivatives throughout an open set
give a local chart whose forward and inverse maps are smooth on their
whole open domains. Pointwise infinite smoothness alone is not used to
infer neighborhood infinite smoothness. -/
theorem exists_smooth_local_chart_on {N : ℕ}
    (θ : (Fin N → ℝ) → (Fin N → ℝ)) {U : Set (Fin N → ℝ)}
    (hU : IsOpen U) (hθ : ContDiffOn ℝ (⊤ : ℕ∞) θ U)
    (hi : ∀ y ∈ U, Function.Injective (fderiv ℝ θ y)) (x : Fin N → ℝ) (hx : x ∈ U) :
    ∃ e : OpenPartialHomeomorph (Fin N → ℝ) (Fin N → ℝ),
      (e : (Fin N → ℝ) → (Fin N → ℝ)) = θ ∧ x ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (e : (Fin N → ℝ) → (Fin N → ℝ)) e.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target := by
  obtain ⟨e,he,hxe,_⟩ := exists_local_chart_of_injective_derivative θ x
    (hθ.contDiffAt (hU.mem_nhds hx)) (hi x hx)
  let f := e.restrOpen U hU
  have hf : (f : (Fin N → ℝ) → (Fin N → ℝ)) = θ := by
    rw [show (f : (Fin N → ℝ) → (Fin N → ℝ)) = e from rfl,he]
  have hsub : f.source ⊆ U := inter_subset_right
  refine ⟨f,hf,⟨hxe,hx⟩,hsub,?_,?_⟩
  · rw [hf]
    exact hθ.mono hsub
  · intro q hq
    have hp := hsub (f.map_target hq)
    have hc := hθ.contDiffAt (hU.mem_nhds hp)
    let B := (LinearEquiv.ofInjectiveEndo (fderiv ℝ θ (f.symm q)).toLinearMap
      (hi _ hp)).toContinuousLinearEquiv
    have hd : HasFDerivAt f (B : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (f.symm q) := by
      rw [hf]
      exact (hc.differentiableAt (by simp)).hasFDerivAt
    exact (f.contDiffAt_symm hq hd (by simpa only [hf] using hc)).contDiffWithinAt
end RothschildStein.L1

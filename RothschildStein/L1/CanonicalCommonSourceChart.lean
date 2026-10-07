-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CanonicalSmoothLocalCharts
public import RothschildStein.L1.CanonicalExponential

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RothschildStein.L1.CanonicalFrameChartData

/-- Local coordinate inverses give
an open image for every open subset of the common spatial patch. -/
theorem isOpen_theta_image {N : ℕ} {Ω : Set (Fin N → ℝ)}
    {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}
    (C : CanonicalFrameChartData Ω Y x) {U : Set (Fin N → ℝ)}
    (hU : IsOpen U) (hsub : U ⊆ ball x C.radius)
    {η : Fin N → ℝ} (hη : η ∈ ball x C.radius) :
    IsOpen ((fun ξ => C.theta (η,ξ)) '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro u ⟨ξ,hξ,rfl⟩
  obtain ⟨e,he,hξe,_,_,_⟩ := C.theta_right_smooth_localChart η ξ hη (hsub hξ)
  have hopen := e.isOpen_image_source_inter hU
  have hm : C.theta (η,ξ) ∈ e '' (e.source ∩ U) := by
    exact ⟨ξ,⟨hξe,hξ⟩,congrFun he ξ⟩
  apply Filter.mem_of_superset (hopen.mem_nhds hm)
  rintro v ⟨z,hz,rfl⟩
  exact ⟨z,hz.2,(congrFun he z).symm⟩

/-- One open spatial patch is the
exact source of every canonical coordinate homeomorphism. The inverse
is the actual canonical exponential on its entire image. -/
theorem exists_common_source_chart {N : ℕ} {Ω : Set (Fin N → ℝ)}
    {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}
    (C : CanonicalFrameChartData Ω Y x) {U : Set (Fin N → ℝ)}
    (hU : IsOpen U) (hsub : U ⊆ ball x C.radius)
    {η : Fin N → ℝ} (hη : η ∈ ball x C.radius) :
    ∃ e : OpenPartialHomeomorph (Fin N → ℝ) (Fin N → ℝ),
      e.source = U ∧ e.target = (fun ξ => C.theta (η,ξ)) '' U ∧
      (∀ ξ, e ξ = C.theta (η,ξ)) ∧
      (∀ u, e.symm u = canonicalFrameMap C.time C.flow (η,u)) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target := by
  let f := fun ξ => C.theta (η,ξ)
  let g := fun u => canonicalFrameMap C.time C.flow (η,u)
  have hleft : ∀ ξ ∈ U, g (f ξ) = ξ := fun ξ hξ =>
    C.right_inverse (η,ξ) (C.basePatch_subset ⟨hη,hsub hξ⟩)
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) f U := by
    intro ξ hξ
    exact (C.theta_right_contDiffAt η ξ hη (hsub hξ)).contDiffWithinAt
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g (f '' U) := by
    rintro u ⟨ξ,hξ,rfl⟩
    exact (C.forward_at_inverse_contDiffAt η ξ hη (hsub hξ)).contDiffWithinAt
  let e : OpenPartialHomeomorph (Fin N → ℝ) (Fin N → ℝ) := {
    toFun := f
    invFun := g
    source := U
    target := f '' U
    map_source' := fun ξ hξ => ⟨ξ,hξ,rfl⟩
    map_target' := by
      rintro u ⟨ξ,hξ,rfl⟩
      simpa only [hleft ξ hξ] using hξ
    left_inv' := hleft
    right_inv' := by
      rintro u ⟨ξ,hξ,rfl⟩
      rw [hleft ξ hξ]
    continuousOn_toFun := hf.continuousOn
    continuousOn_invFun := hg.continuousOn
    open_source := hU
    open_target := C.isOpen_theta_image hU hsub hη }
  exact ⟨e,rfl,rfl,fun _ => rfl,fun _ => rfl,hf,hg⟩

end RothschildStein.L1.CanonicalFrameChartData

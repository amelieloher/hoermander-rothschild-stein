-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CanonicalFullTargetRadial
public import RothschildStein.L1.CanonicalTargetDomainOpen
public import RothschildStein.L1.CanonicalChartSmallPatch

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators
namespace RothschildStein.L1.CanonicalFrameChartData

/-- A canonical flow constructs
one relatively compact common spatial source within a prescribed ball, the complete target
family, whole-target smooth inverses and radial trajectories. -/
theorem exists_common_patch_with_radius {N : ℕ} {Ω : Set (Fin N → ℝ)}
    {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}
    (C : CanonicalFrameChartData Ω Y x) (R : ℝ) (hR : 0 < R) :
    ∃ U : Set (Fin N → ℝ), ∃ e : (Fin N → ℝ) →
        OpenPartialHomeomorph (Fin N → ℝ) (Fin N → ℝ),
      IsOpen U ∧ IsCompact (closure U) ∧ closure U ⊆ Ω ∧ x ∈ U ∧ U ⊆ ball x R ∧
      U ⊆ ball x (C.radius/2) ∧
      (∀ η ∈ U, ∀ ξ ∈ U, C.theta (η,ξ) ∈ ball 0 (C.radius/2)) ∧
      (∀ η ∈ U, (e η).source = U ∧
        (e η).target = (fun ξ => C.theta (η,ξ)) '' U ∧
        (∀ ξ, e η ξ = C.theta (η,ξ)) ∧
        (∀ u, (e η).symm u = canonicalFrameMap C.time C.flow (η,u)) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (e η) (e η).source ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (e η).symm (e η).target) ∧
      IsOpen {z : (Fin N → ℝ) × (Fin N → ℝ) |
        z.1 ∈ U ∧ z.2 ∈ (e z.1).target} ∧
      (∀ η ∈ U, ∀ u ∈ (e η).target,
        ∃ γ : ℝ → (Fin N → ℝ), γ 0 = η ∧ γ 1 = (e η).symm u ∧
          ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Ω ∧
            HasDerivAt γ (∑ j, u j • Y j (γ t)) t) := by
  classical
  obtain ⟨r,hr,hrC,hsmall⟩ := C.exists_small_base_patch (half_pos C.radius_pos)
  let r' := min (min (r/2) (C.radius/4)) (R/2)
  have hr' : 0 < r' := lt_min (lt_min (half_pos hr) (div_pos C.radius_pos (by norm_num))) (half_pos hR)
  have hrr : r' ≤ r := (min_le_left _ _).trans ((min_le_left _ _).trans (by linarith))
  have hrhalf : r' ≤ C.radius/2 := (min_le_left _ _).trans ((min_le_right _ _).trans (by linarith [C.radius_pos]))
  let U := ball x r'
  have hsubhalf : U ⊆ ball x (C.radius/2) := ball_subset_ball hrhalf
  have hsub : U ⊆ ball x C.radius := hsubhalf.trans (ball_subset_ball (by linarith [C.radius_pos]))
  have hs : ∀ η ∈ U, ∀ ξ ∈ U, C.theta (η,ξ) ∈ ball 0 (C.radius/2) :=
    fun η hη ξ hξ => hsmall η (ball_subset_ball hrr hη) ξ (ball_subset_ball hrr hξ)
  have hs' : ∀ η ∈ U, ∀ ξ ∈ U, C.theta (η,ξ) ∈ ball 0 C.radius :=
    fun η hη ξ hξ => ball_subset_ball (by linarith [C.radius_pos]) (hs η hη ξ hξ)
  let e := fun η => if hη : η ∈ U then
      (C.exists_common_source_chart isOpen_ball hsub (hsub hη)).choose
    else OpenPartialHomeomorph.refl _
  have he : ∀ η ∈ U, (e η).source = U ∧
      (e η).target = (fun ξ => C.theta (η,ξ)) '' U ∧
      (∀ ξ, e η ξ = C.theta (η,ξ)) ∧
      (∀ u, (e η).symm u = canonicalFrameMap C.time C.flow (η,u)) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (e η) (e η).source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (e η).symm (e η).target := by
    intro η hη
    simpa only [e,dite_eq_left hη] using
      (C.exists_common_source_chart isOpen_ball hsub (hsub hη)).choose_spec
  refine ⟨U,e,isOpen_ball,?_,?_,mem_ball_self hr',ball_subset_ball ((min_le_right _ _).trans (half_le_self hR.le)),hsubhalf,hs,he,?_,?_⟩
  · exact (isCompact_closedBall x r').of_isClosed_subset isClosed_closure
      (closure_minimal ball_subset_closedBall isClosed_closedBall)
  · exact (closure_minimal ball_subset_closedBall isClosed_closedBall).trans
      ((closedBall_subset_closedBall (hrr.trans hrC)).trans C.closedPatch_subset)
  · have ht : {z : (Fin N → ℝ) × (Fin N → ℝ) | z.1 ∈ U ∧ z.2 ∈ (e z.1).target} =
        {z | z.1 ∈ U ∧ z.2 ∈ (fun ξ => C.theta (z.1,ξ)) '' U} := by
      ext z
      constructor
      · rintro ⟨hz,hu⟩
        exact ⟨hz,by simpa only [(he z.1 hz).2.1] using hu⟩
      · rintro ⟨hz,hu⟩
        exact ⟨hz,by simpa only [(he z.1 hz).2.1] using hu⟩
    rw [ht]
    exact C.isOpen_total_target isOpen_ball hsub hs'
  · intro η hη u hu
    rw [(he η hη).2.1] at hu
    obtain ⟨γ,hγ0,hγ1,hγ⟩ := C.full_target_radial_curve hsub hs' hη hu
    exact ⟨γ,hγ0,hγ1.trans ((he η hη).2.2.2.1 u).symm,hγ⟩

end RothschildStein.L1.CanonicalFrameChartData

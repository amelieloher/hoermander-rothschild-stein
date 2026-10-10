-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.AlmostEverywhereOrbitPairings
public import HeatKernel.Kernel.CoordinateTestSlices
public import HeatKernel.Kernel.InverseCoordinateMeasure

/-! # Coordinate weak identities from almost-everywhere orbit sections

The volume-preserving time-space equivalence transports the weak time
identity to compact tests on the coordinate vector space.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open RothschildStein

namespace HeatKernel

/-- Almost-everywhere spatial sections suffice to transport an orbit pairing into the coordinate weak identity. -/
theorem integral_coordinate_test_eq_zero_of_ae_orbit_pairing {n : ℕ}
    (I : Opens ℝ) (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (U φ ψ : (Fin (1 + n) → ℝ) → ℝ)
    (hU : LocallyIntegrableOn U {z | z 0 ∈ I} volume)
    (hae : ∀ᵐ t ∂volume, t ∈ I →
      (fun x => U ((timeSpaceCoordinates n).symm (t, x))) =ᵐ[volume] u t)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ {z | z 0 ∈ I})
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ {z | z 0 ∈ I})
    (hu : ContDiffOn ℝ 1 u (I : Set ℝ))
    (hpair : ∀ t, inner ℝ (deriv u t)
      ((memLp_two_coordinate_test_slice φ hφ hcφ t).toLp
        (fun x => φ ((timeSpaceCoordinates n).symm (t, x)))) =
      inner ℝ (u t) ((memLp_two_coordinate_test_slice ψ hψ hcψ t).toLp
        (fun x => ψ ((timeSpaceCoordinates n).symm (t, x))))) :
    Integrable (fun z => U z *
      (fderiv ℝ φ z (leftCoordinateInclusion 1 n (fun _ => 1)) + ψ z)) ∧
      (∫ z, U z * (fderiv ℝ φ z (leftCoordinateInclusion 1 n (fun _ => 1)) + ψ z)) = 0 := by
  let E := timeSpaceCoordinates n
  let Φ := φ ∘ E.symm
  let Ψ := ψ ∘ E.symm
  obtain ⟨hΦ, hcΦ⟩ := smooth_compact_inverse_timeSpace_test φ hφ hcφ
  obtain ⟨hΨ, hcΨ⟩ := smooth_compact_inverse_timeSpace_test ψ hψ hcψ
  have hsΦ : tsupport Φ ⊆ (I : Set ℝ) ×ˢ Set.univ := by
    intro p hp
    have h := hsφ (tsupport_comp_subset_preimage φ E.symm.continuous hp)
    change E.symm (p.1, p.2) 0 ∈ I at h
    refine ⟨?_, Set.mem_univ _⟩
    change p.1 ∈ I
    simpa only [E, timeSpaceCoordinates_symm_time] using h
  have hsΨ : tsupport Ψ ⊆ (I : Set ℝ) ×ˢ Set.univ := by
    intro p hp
    have h := hsψ (tsupport_comp_subset_preimage ψ E.symm.continuous hp)
    change E.symm (p.1, p.2) 0 ∈ I at h
    refine ⟨?_, Set.mem_univ _⟩
    change p.1 ∈ I
    simpa only [E, timeSpaceCoordinates_symm_time] using h
  have hpre : E.symm ⁻¹' {z | z 0 ∈ I} = (I : Set ℝ) ×ˢ Set.univ := by
    ext p
    change (E.symm (p.1, p.2) 0 ∈ I) ↔ _
    simp only [E, timeSpaceCoordinates_symm_time, Set.mem_prod, Set.mem_univ, and_true]
    rfl
  have hUp : LocallyIntegrableOn (U ∘ E.symm) ((I : Set ℝ) ×ˢ Set.univ) volume := by
    have h := locallyIntegrableOn_comp_inverse_timeSpaceCoordinates n
      (I.isOpen.preimage (continuous_apply 0)) hU
    change LocallyIntegrableOn (U ∘ E.symm) (E.symm ⁻¹' {z | z 0 ∈ I}) volume at h
    rwa [hpre] at h
  have hweak := integral_spacetime_test_eq_zero_of_ae_orbit_pairing I u (U ∘ E.symm)
    Φ Ψ hUp hae hΦ hcΦ hsΦ hΨ.continuous hcΨ hsΨ hu hpair
  have heq : (fun z => U z *
      (fderiv ℝ φ z (leftCoordinateInclusion 1 n (fun _ => 1)) + ψ z)) =
      (fun p => U (E.symm p) * (fderiv ℝ Φ p (1, 0) + Ψ p)) ∘ E := by
    funext z
    change _ = U (E.symm (E z)) *
      (fderiv ℝ (φ ∘ E.symm) (E z) (1, 0) + ψ (E.symm (E z)))
    rw [fderiv_inverse_timeSpace_test_time φ (E z)
      (hφ.differentiable (by simp) (E.symm (E z)))]
    simp only [E, ContinuousLinearEquiv.symm_apply_apply]
  rw [heq]
  refine ⟨?_, ?_⟩
  · exact ((measurePreserving_timeSpaceCoordinates n).integrable_comp_emb
      E.toHomeomorph.measurableEmbedding).mpr hweak.1
  · exact (integral_timeSpaceCoordinates n _).trans hweak.2

end HeatKernel

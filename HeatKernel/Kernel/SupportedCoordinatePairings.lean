-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CoordinateTestSlices

/-! # Coordinate pairings supported in a time domain

Compact coordinate tests supported in a time domain define zero L²
slices outside it. Generator pairing identities therefore need only
be supplied inside the time domain.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace

namespace HeatKernel

/-- A coordinate test supported in a time domain has zero spatial slices outside it. -/
theorem coordinate_test_slice_eq_zero_outside_time_domain {n : ℕ}
    (I : Set ℝ) (φ : (Fin (1 + n) → ℝ) → ℝ)
    (hs : tsupport φ ⊆ {z | z 0 ∈ I}) {t : ℝ} (ht : t ∉ I) :
    (fun x => φ ((timeSpaceCoordinates n).symm (t, x))) = 0 := by
  funext x
  apply image_eq_zero_of_notMem_tsupport
  intro hz
  have h := hs hz
  change (timeSpaceCoordinates n).symm (t, x) 0 ∈ I at h
  rw [timeSpaceCoordinates_symm_time] at h
  exact ht h

/-- The L² slice of a supported coordinate test is zero outside its time domain. -/
theorem toLp_coordinate_test_slice_eq_zero_outside_time_domain {n : ℕ}
    (I : Set ℝ) (φ : (Fin (1 + n) → ℝ) → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {z | z 0 ∈ I}) {t : ℝ} (ht : t ∉ I) :
    (memLp_two_coordinate_test_slice φ hφ hc t).toLp
      (fun x => φ ((timeSpaceCoordinates n).symm (t, x))) = 0 := by
  apply toLp_two_eq_zero_of_ae_eq_zero
  exact Filter.Eventually.of_forall fun x =>
    congrFun (coordinate_test_slice_eq_zero_outside_time_domain I φ hs ht) x

/-- Generator pairings against supported coordinate tests extend automatically outside the time domain. -/
theorem coordinate_orbit_pairing_of_pairing_on_time_domain {n : ℕ}
    (I : Set ℝ) (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (φ ψ : (Fin (1 + n) → ℝ) → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ {z | z 0 ∈ I})
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ {z | z 0 ∈ I})
    (hpair : ∀ t ∈ I, inner ℝ (deriv u t)
      ((memLp_two_coordinate_test_slice φ hφ hcφ t).toLp
        (fun x => φ ((timeSpaceCoordinates n).symm (t, x)))) =
      inner ℝ (u t) ((memLp_two_coordinate_test_slice ψ hψ hcψ t).toLp
        (fun x => ψ ((timeSpaceCoordinates n).symm (t, x))))) :
    ∀ t, inner ℝ (deriv u t)
      ((memLp_two_coordinate_test_slice φ hφ hcφ t).toLp
        (fun x => φ ((timeSpaceCoordinates n).symm (t, x)))) =
      inner ℝ (u t) ((memLp_two_coordinate_test_slice ψ hψ hcψ t).toLp
        (fun x => ψ ((timeSpaceCoordinates n).symm (t, x)))) := by
  intro t
  by_cases ht : t ∈ I
  · exact hpair t ht
  · rw [toLp_coordinate_test_slice_eq_zero_outside_time_domain I φ hφ hcφ hsφ ht,
      toLp_coordinate_test_slice_eq_zero_outside_time_domain I ψ hψ hcψ hsψ ht,
      inner_zero_right, inner_zero_right]

end HeatKernel

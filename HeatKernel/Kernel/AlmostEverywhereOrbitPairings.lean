-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.SmoothSpacetimeOrbitTests
public import HeatKernel.Kernel.L2ScalarPairings
public import HeatKernel.Kernel.CompactTestIntegrability
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Spacetime identities from almost-everywhere orbit sections

Local integrability and a spatial representative identity promote the
integrated Hilbert-space time identity to a spacetime integral identity.
The generator pairing remains an explicit hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace

namespace HeatKernel

/-- Almost-everywhere time sections suffice for the spacetime identity of a differentiable L² orbit. -/
theorem integral_spacetime_test_eq_zero_of_ae_orbit_pairing {n : ℕ}
    (I : Opens ℝ) (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (U φ ψ : ℝ × (Fin n → ℝ) → ℝ)
    (hU : LocallyIntegrableOn U ((I : Set ℝ) ×ˢ Set.univ) volume)
    (hae : ∀ᵐ t ∂volume, t ∈ I → (fun x => U (t, x)) =ᵐ[volume] u t)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ (I : Set ℝ) ×ˢ Set.univ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (I : Set ℝ) ×ˢ Set.univ)
    (hu : ContDiffOn ℝ 1 u (I : Set ℝ))
    (hpair : ∀ t, inner ℝ (deriv u t)
      ((memLp_two_spatial_slice φ hφ.continuous hcφ t).toLp (fun x => φ (t, x))) =
      inner ℝ (u t) ((memLp_two_spatial_slice ψ hψ hcψ t).toLp (fun x => ψ (t, x)))) :
    Integrable (fun z => U z * (fderiv ℝ φ z (1, 0) + ψ z)) ∧
      (∫ z, U z * (fderiv ℝ φ z (1, 0) + ψ z)) = 0 := by
  let D : ℝ × (Fin n → ℝ) → ℝ := fun z => fderiv ℝ φ z (1, 0)
  have hD : Continuous D := continuous_spacetime_time_differential φ hφ
  have hcD : HasCompactSupport D := hcφ.fderiv_apply (𝕜 := ℝ) (1, 0)
  have hsD : tsupport D ⊆ (I : Set ℝ) ×ˢ Set.univ :=
    (tsupport_fderiv_apply_subset ℝ (1, 0)).trans hsφ
  have hweak := integral_inner_orbit_smooth_spacetime_test_eq_zero I u
    (fun t => (memLp_two_spatial_slice ψ hψ hcψ t).toLp (fun x => ψ (t, x)))
    φ hφ hcφ hsφ hu hpair
  have hscalar := integral_scalar_pairing_eq_zero_of_inner_pairing u
    (fun t x => D (t, x)) (fun t x => ψ (t, x))
    (memLp_two_spatial_slice D hD hcD) (memLp_two_spatial_slice ψ hψ hcψ) hweak
  have hiD := integrable_mul_compact_test_of_locallyIntegrableOn hU hD hcD hsD
  have hiψ := integrable_mul_compact_test_of_locallyIntegrableOn hU hψ hcψ hsψ
  have hint : Integrable (fun z => U z * (D z + ψ z)) := by
    have hsum : Integrable (fun z => U z * D z + U z * ψ z) := hiD.add hiψ
    simpa only [mul_add] using hsum
  refine ⟨hint, ?_⟩
  have heq : (fun t => ∫ x, U (t, x) * (D (t, x) + ψ (t, x))) =ᵐ[volume]
      (fun t => ∫ x, u t x * (D (t, x) + ψ (t, x))) := by
    filter_upwards [hae] with t htAE
    by_cases ht : t ∈ I
    · apply integral_congr_ae
      filter_upwards [htAE ht] with x hx
      rw [hx]
    · have hzD (x : Fin n → ℝ) : D (t, x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => ht (hsD h).1)
      have hzψ (x : Fin n → ℝ) : ψ (t, x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => ht (hsψ h).1)
      simp only [hzD, hzψ, add_zero, mul_zero, integral_zero]
  have hprod : Integrable (fun z => U z * (D z + ψ z))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    simpa only [Measure.volume_eq_prod] using hint
  change (∫ z, U z * (D z + ψ z)) = 0
  rw [Measure.volume_eq_prod, integral_prod _ hprod]
  exact (integral_congr_ae heq).trans hscalar.2

end HeatKernel

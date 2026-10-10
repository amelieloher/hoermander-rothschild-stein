-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CoordinateHorizontalResolventTests
public import HeatKernel.Kernel.ResolventOrbitPairings
public import HeatKernel.Kernel.SupportedCoordinatePairings
public import HeatKernel.Kernel.AlmostEverywhereCoordinatePairings

/-! # Horizontal heat tests from almost-everywhere orbit sections -/

@[expose] public section

noncomputable section

open MeasureTheory RothschildStein

namespace HeatKernel

/-- Concrete horizontal resolvent orbits and almost-everywhere time sections give the compact adjoint heat identity. -/
theorem setIntegral_positive_heat_test_eq_zero_of_ae_horizontal_resolvent_orbit {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (U φ : (Fin (1 + n) → ℝ) → ℝ)
    (hU : LocallyIntegrableOn U {z | 0 < z 0} volume)
    (hslice : ∀ᵐ t ∂volume, 0 < t →
      (fun x => U ((timeSpaceCoordinates n).symm (t, x))) =ᵐ[volume] u t)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {z | 0 < z 0}) (hC : ContDiffOn ℝ 1 u (Set.Ioi 0))
    (horbit : ∀ t, 0 < t →
      InverseResolventGraph (globalHorizontalFormResolvent G hq) (u t) (-deriv u t)) :
    Integrable (fun z => U z *
      (fderiv ℝ φ z (leftCoordinateInclusion 1 n (fun _ => 1)) +
        sumSquares (fun i => liftRightField 1 (G.horizontalFields hq i)) φ z)) ∧
      (∫ z in {z | 0 < z 0}, U z *
        (fderiv ℝ φ z (leftCoordinateInclusion 1 n (fun _ => 1)) +
          sumSquares (fun i => liftRightField 1 (G.horizontalFields hq i)) φ z)) = 0 := by
  let X := G.horizontalFields hq
  let ψ := sumSquares (fun i => liftRightField 1 (X i)) φ
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    contDiff_sumSquares_of_contDiff _
      (fun i => (G.horizontalFields_contDiff hq i).liftRightField 1) φ hφ
  have hcψ : HasCompactSupport ψ := hasCompactSupport_sumSquares _ φ hc
  have hsψ : tsupport ψ ⊆ {z | 0 < z 0} := (tsupport_sumSquares_subset _ φ).trans hs
  have hpair := coordinate_orbit_pairing_of_pairing_on_time_domain (Set.Ioi 0) u φ ψ
    hφ hc hs hψ hcψ hsψ (fun t ht =>
      inner_orbit_derivative_test_eq_of_resolvent_graph
        (globalHorizontalFormResolvent G hq) (globalHorizontalFormResolvent_isSelfAdjoint G hq)
        (horbit t ht)
        (inverseResolventGraph_globalHorizontalForm_coordinate_test_slice G hq φ hφ hc t ht))
  have hfull := integral_coordinate_test_eq_zero_of_ae_orbit_pairing
    (⟨Set.Ioi 0, isOpen_Ioi⟩ : TopologicalSpace.Opens ℝ) u U φ ψ hU hslice
    hφ hc hs hψ hcψ hsψ hC hpair
  refine ⟨hfull.1, ?_⟩
  change (∫ z in {z | 0 < z 0}, U z *
    (fderiv ℝ φ z (leftCoordinateInclusion 1 n (fun _ => 1)) + ψ z)) = 0
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hfull.2
  · intro z hz
    have hnot : z ∉ tsupport φ := fun h => hz (hs h)
    have hzψ : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hsψ h))
    rw [fderiv_of_notMem_tsupport ℝ hnot, zero_apply, hzψ, add_zero, mul_zero]

end HeatKernel

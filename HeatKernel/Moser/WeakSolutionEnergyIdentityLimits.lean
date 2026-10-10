-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionNonlinearIdentity
public import HeatKernel.Moser.WeakSolutionScalarTests
public import HeatKernel.Moser.NonlinearAveragePairingLimits
public import HeatKernel.Moser.PointwiseAverageLimits

/-! # Passing regularized nonlinear energy identities to endpoint identities

Strong flux-pairing convergence and almost-everywhere convergence of the energy
endpoints remove the averaging scale. The fixed-scale regularized equation is an
explicit hypothesis. The sign corresponds to a positive spatial energy flux.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace HeatKernel

/-- For almost every pair of endpoints, a regularized nonlinear energy equation
passes to its original endpoint and flux integrals. The same full-measure endpoint
set works for every continuous energy and every continuous test of linear growth. -/
theorem ae_energy_endpoint_identity_of_regularized {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {v : ℝ → E} (hv : MemLp v 2 volume) :
    ∀ᵐ a ∂volume, ∀ᵐ b ∂volume,
      ∀ (I : Set ℝ), IsOpen I →
      ∀ F : ℝ → (E →L[ℝ] ℝ), MemLp F 2 (volume.restrict I) →
      ∀ (P : E → E), Continuous P →
      ∀ C : ℝ≥0, (∀ z, ‖P z‖ ≤ C * ‖z‖) →
      ∀ (Φ : E → ℝ), Continuous Φ →
      a ≤ b → Icc a b ⊆ I →
      (∃ δ : ℝ, 0 < δ ∧ ∀ h ∈ Ioo 0 δ,
        Φ (forwardTimeAverage h v a) - Φ (forwardTimeAverage h v b) =
          ∫ t in Icc a b, forwardTimeAverage h F t (P (forwardTimeAverage h v t))) →
      Φ (v a) - Φ (v b) = ∫ t in Icc a b, F t (P (v t)) := by
  have hlim := ae_tendsto_forwardTimeAverage (hv.locallyIntegrable (by norm_num))
  filter_upwards [hlim] with a ha
  filter_upwards [hlim] with b hb
  intro I hI F hF P hP C hC Φ hΦ _ hsub hreg
  have henergy := (hΦ.continuousAt.tendsto.comp ha).sub (hΦ.continuousAt.tendsto.comp hb)
  have hvI : MemLp v 2 (volume.restrict I) := hv.mono_measure Measure.restrict_le_self
  have hflux := tendsto_integral_forwardTimeAverage_dual_comp hI isCompact_Icc hsub hvI hF hP hC
  obtain ⟨δ, hδ, hreg⟩ := hreg
  apply nonlinear_energy_integral_eq_of_regularized_limits henergy hflux
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hδ).filter_mono inf_le_left] with h hh hsmall
  exact hreg h ⟨hh, hsmall⟩

end HeatKernel

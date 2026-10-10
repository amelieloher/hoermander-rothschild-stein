-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.RepresentativeDualPairingLimits
public import HeatKernel.Bridge.HilbertDualTimeAverages
public import HeatKernel.Form.TimeAverageCompositionLimits

/-! # Removing time averages from fixed spatial tests

Strong local square-integrable convergence of the flux gives convergence of its
pairing with a fixed form-domain test on every compact interior time set.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace HeatKernel

/-- A fixed form-domain test can be paired with averaged dual fluxes and passed
to the unregularized limit on compact interior time sets. -/
theorem tendsto_integral_forwardTimeAverage_fixed_test {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {I K : Set ℝ} (hI : IsOpen I) (hK : IsCompact K) (hKI : K ⊆ I)
    {F : ℝ → (E →L[ℝ] ℝ)} (hF : MemLp F 2 (volume.restrict I)) (w : E) :
    Tendsto (fun h => ∫ t in K, forwardTimeAverage h F t w) (𝓝[>] 0)
      (𝓝 (∫ t in K, F t w)) := by
  let : InnerProductSpace ℝ (E →L[ℝ] ℝ) := hilbertDualInnerProductSpace E
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hw : MemLp (fun _ : ℝ => w) 2 (volume.restrict K) := memLp_const w
  have hFm := (eventually_memLp_timeAverages_restrict hI hK hKI hF).mono fun _ hh => hh.1
  exact tendsto_integral_dual_apply_of_eventually_memLp hFm (Eventually.of_forall fun _ => hw)
    (hF.mono_measure (Measure.restrict_mono hKI le_rfl)) hw
    (tendsto_eLpNorm_forwardTimeAverage_sub_restrict hI hK hKI hF)
    (by simp only [sub_self, eLpNorm_zero]; exact tendsto_const_nhds)

/-- Fixed-test endpoint identities transfer between curves agreeing on the
compact time interval. The endpoints remain strictly inside that interval. -/
theorem ae_linear_endpoint_identity_of_eqOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] (E →L[ℝ] ℝ)) {v w : ℝ → E} {F : ℝ → (E →L[ℝ] ℝ)} {A B : ℝ}
    (heq : EqOn v w (Icc A B))
    (hv : ∀ᵐ a ∂volume, ∀ᵐ b ∂volume, ∀ z : E, a ≤ b → A < a → b < B →
      D (v a) z - D (v b) z = ∫ t in Icc a b, F t z) :
    ∀ᵐ a ∂volume, ∀ᵐ b ∂volume, ∀ z : E, a ≤ b → A < a → b < B →
      D (w a) z - D (w b) z = ∫ t in Icc a b, F t z := by
  filter_upwards [hv] with a ha
  filter_upwards [ha] with b hb
  intro z hab hAa hbB
  have haAB : a ∈ Icc A B := ⟨hAa.le, hab.trans hbB.le⟩
  have hbAB : b ∈ Icc A B := ⟨hAa.le.trans hab, hbB.le⟩
  have he := hb z hab hAa hbB
  rwa [heq haAB, heq hbAB] at he

end HeatKernel

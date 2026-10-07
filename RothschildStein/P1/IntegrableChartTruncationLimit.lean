-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RightParametrixTransport
public import RothschildStein.P1.GaugeChartIntegrability
public import RothschildStein.P1.AmbientTruncationLocalization
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- Integrable input rows supported in the chart
converge under actual ambient gauge truncation, without global regularity
of the chart map. -/
theorem tendsto_integrableChart_truncation
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    {f : (Fin (n + m) → ℝ) → ℝ} (hf : Integrable f volume)
    (hs : ∀ η, η ∉ C.U → f η = 0) :
    Tendsto (fun ε : ℝ => ∫ η in {η | ε < ν (C.Θ η ξ)}, f η)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ η, f η)) := by
  let rsChartTruncationFinNonempty : Nonempty (Fin (n + m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  let A := fun ε : ℝ => C.U ∩ {η | ε < ν (C.Θ η ξ)}
  have hθ : ContinuousOn (fun η => C.Θ η ξ) C.U := (C.contDiffOn_Θ_fst hξ).continuousOn
  have hA (ε : ℝ) : MeasurableSet (A ε) :=
    ((hν.1.comp_continuousOn hθ).isOpen_inter_preimage C.isOpen_U isOpen_Ioi).measurableSet
  have ht : Tendsto (fun ε : ℝ => ∫ η, (A ε).indicator f η)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ η, f η)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun η => ‖f η‖)
    · exact Eventually.of_forall (fun ε => (hf.indicator (hA ε)).aestronglyMeasurable)
    · exact Eventually.of_forall (fun ε => ae_of_all _ (fun η => norm_indicator_le_norm_self _ _))
    · exact hf.norm
    · filter_upwards [volume.ae_ne ξ] with η hne
      by_cases hη : η ∈ C.U
      · have hu : C.Θ η ξ ≠ 0 := (C.theta_eq_zero_iff hη hξ).not.mpr hne.symm
        have hp : 0 < ν (C.Θ η ξ) := lt_of_le_of_ne (hν.2.1 _)
          (Ne.symm (fun hz => hu ((hν.2.2.1 _).mp hz)))
        have heps : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < ν (C.Θ η ξ) :=
          (eventually_lt_nhds hp).filter_mono nhdsWithin_le_nhds
        apply tendsto_const_nhds.congr'
        filter_upwards [heps] with ε hε
        exact (indicator_of_mem (show η ∈ A ε from ⟨hη, hε⟩) f).symm
      · have hz := hs η hη
        apply tendsto_const_nhds.congr'
        filter_upwards with ε
        simp [A, hη, hz]
  refine ht.congr' (Eventually.of_forall (fun ε => ?_))
  rw [integral_indicator (hA ε)]
  change (∫ η in C.U ∩ {η | ε < ν (C.Θ η ξ)}, f η) =
    ∫ η in {η | ε < ν (C.Θ η ξ)}, f η
  simpa only [inter_comm] using
    integral_localizedTruncation (A := {η | ε < ν (C.Θ η ξ)}) C.isOpen_U.measurableSet hs

end RothschildStein.P1.LiftedChart

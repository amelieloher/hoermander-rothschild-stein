-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SharpInputChartTransport
public import RothschildStein.H1.PuncturedProductIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- Every positive sharp input-chart truncation
of a punctured continuous model kernel against a compact test is integrable. -/
theorem integrableOn_sharp_inputChart {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {ν κ : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (hκ : ContinuousOn κ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun η => κ (C.Θ η ξ) * ψ η)
      (C.U ∩ {η | ε < ν (C.Θ η ξ)}) volume := by
  obtain ⟨hc, hs⟩ := reflectedTransport_regular hξ ψ
  have hz : ν (0 : Fin (n + m) → ℝ) = 0 := (hν.2.2.1 0).mpr rfl
  have hi := (H1.integrableOn_punctured_mul_compact hκ hc.continuous hs
    (isClosed_le continuous_const hν.1)
    (show (0 : Fin (n + m) → ℝ) ∉ {u | ε ≤ ν u} by
      simpa only [mem_ofPred_eq, hz] using not_le.mpr hε)).mono_set
      (show {u | ε < ν u} ⊆ {u | ε ≤ ν u} by
        intro u hu
        change ε < ν u at hu
        change ε ≤ ν u
        exact hu.le)
  have hm : MeasurableSet {u | ε < ν u} :=
    measurableSet_lt measurable_const hν.1.measurable
  have hwhole := hi.integrable_indicator hm
  have he : (fun u => {v | ε < ν v}.indicator
      (fun v => κ v * C.reflectedTransport ξ ψ v) u) =
      (fun u => ({v | ε < ν v}.indicator κ) u * C.reflectedTransport ξ ψ u) := by
    funext u
    by_cases hu : ε < ν u <;> simp [hu]
  change Integrable (fun u => {v | ε < ν v}.indicator
    (fun v => κ v * C.reflectedTransport ξ ψ v) u) volume at hwhole
  rw [he] at hwhole
  have hneg := (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hwhole
  have hmodel : Integrable (fun u => ({v | ε < ν v}.indicator κ) (-u) *
      C.modelTransport ξ ψ u) volume := by
    simpa only [Function.comp_def, reflectedTransport, neg_neg] using hneg
  have hchart := (integrableOn_comp_theta_mul_iff hξ
    (fun u => ({v | ε < ν v}.indicator κ) (-u)) ψ).mpr hmodel
  have hθ : ContinuousOn (fun η => C.Θ η ξ) C.U :=
    (C.theta_smooth.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun η hη => ⟨hη, hξ⟩)).continuousOn
  have hmi : MeasurableSet (C.U ∩ {η | ε < ν (C.Θ η ξ)}) :=
    ((hν.1.comp_continuousOn hθ).isOpen_inter_preimage C.isOpen_U isOpen_Ioi).measurableSet
  have hfull := hchart.integrable_indicator C.isOpen_U.measurableSet
  rw [← integrable_indicator_iff hmi]
  refine hfull.congr (ae_of_all _ (fun η => ?_))
  by_cases hη : η ∈ C.U
  · rw [indicator_of_mem hη]
    rw [← C.theta_antisymm ξ hξ η hη]
    by_cases ht : ε < ν (C.Θ η ξ) <;> simp [hη, ht]
  · simp [hη]

end RothschildStein.P1.LiftedChart

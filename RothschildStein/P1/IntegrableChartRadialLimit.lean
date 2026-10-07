-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.IntegrableChartTruncationLimit

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

/-- Smooth radial exterior cutoffs pass to the full
integral of an integrable supported chart row for the prescribed gauge. -/
theorem tendsto_integrableChart_radialCutoff
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    {f : (Fin (n + m) → ℝ) → ℝ} (hf : Integrable f volume)
    (hs : ∀ η, η ∉ C.U → f η = 0)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {R : ℝ} (hR : 0 < R)
    (hout : ∀ t : ℝ, R ≤ t → Φ t = 0) (hb : ∀ u, ‖Φ (ν u)‖ ≤ 1) :
    Tendsto (fun ε : ℝ => ∫ η,
      (1 - Φ (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))) * f η)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ η, f η)) := by
  let rsRadialChartFinNonempty : Nonempty (Fin (n + m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  have hθ : ContinuousOn (fun η => C.Θ η ξ) C.U := (C.contDiffOn_Θ_fst hξ).continuousOn
  have hm (ε : ℝ) : AEStronglyMeasurable
      (fun η => (1 - Φ (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))) * f η) (volume.restrict C.U) := by
    have hc := hΦ.comp_continuousOn (hν.1.comp_continuousOn
      ((G2.continuous_dilate C.G ε⁻¹).comp_continuousOn hθ))
    exact ((continuousOn_const.sub hc).aestronglyMeasurable C.isOpen_U.measurableSet).mul
      hf.integrableOn.aestronglyMeasurable
  have ht : Tendsto (fun ε : ℝ => ∫ η in C.U,
      (1 - Φ (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))) * f η)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ η in C.U, f η)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun η => 2 * ‖f η‖)
    · exact Eventually.of_forall hm
    · apply Eventually.of_forall
      intro ε
      apply ae_of_all
      intro η
      have hc : ‖(1 : ℝ) - Φ (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))‖ ≤ 2 := by
        have hn := norm_sub_le (1 : ℝ) (Φ (ν (C.G.dilate ε⁻¹ (C.Θ η ξ))))
        have hh := hb (C.G.dilate ε⁻¹ (C.Θ η ξ))
        norm_num only [norm_one] at hn
        linarith
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    · exact hf.norm.integrableOn.const_mul 2
    · filter_upwards [ae_restrict_mem C.isOpen_U.measurableSet,
        ae_restrict_of_ae (volume.ae_ne ξ)] with η hη hne
      have hu : C.Θ η ξ ≠ 0 := (C.theta_eq_zero_iff hη hξ).not.mpr hne.symm
      have hp : 0 < ν (C.Θ η ξ) := lt_of_le_of_ne (hν.2.1 _)
        (Ne.symm (fun hz => hu ((hν.2.2.1 _).mp hz)))
      have heps : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < ν (C.Θ η ξ) / R :=
        (eventually_lt_nhds (div_pos hp hR)).filter_mono nhdsWithin_le_nhds
      apply tendsto_const_nhds.congr'
      filter_upwards [heps, self_mem_nhdsWithin] with ε hε hεpos
      have hεR : ε * R < ν (C.Θ η ξ) := (lt_div_iff₀ hR).mp hε
      have hd : R ≤ ν (C.Θ η ξ) / ε := (le_div_iff₀ hεpos).mpr (by nlinarith)
      have hlarge : R ≤ ν (C.G.dilate ε⁻¹ (C.Θ η ξ)) := by
        rw [hν.2.2.2 ε⁻¹ (inv_pos.mpr hεpos)]
        simpa only [div_eq_mul_inv, mul_comm] using hd
      rw [hout _ hlarge]
      simp only [sub_zero, one_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hs] at ht
  refine ht.congr' (Eventually.of_forall (fun ε => ?_))
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun η hη => by rw [hs η hη, mul_zero])

end RothschildStein.P1.LiftedChart

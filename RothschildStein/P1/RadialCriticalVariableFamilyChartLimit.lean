-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.CriticalVariableFamilyChartLimit
public import RothschildStein.P1.IntegrableChartRadialLimit
public import RothschildStein.P1.RadialCriticalChartLimit
public import RothschildStein.H1.ContinuousPuncturedCutoff

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
  {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}

/-- Smooth radial regularization of the actual
variable critical family has the same value as its prescribed sharp
principal value, including the full endpoint-freezing error. -/
theorem tendsto_radialCriticalVariableFamily_inputChart
    (F : SplitFamily C.G D) (Γ : (Fin (n + m) → ℝ) → ℝ)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      Γ (C.G.dilate t u) = t ^ (2 - (C.G.homogeneousDimension : ℝ)) * Γ u)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hone : ∀ t : ℝ, t < r → Φ t = 1)
    (hout : ∀ t : ℝ, R ≤ t → Φ t = 0) (hb : ∀ u, ‖Φ (ν u)‖ ≤ 1)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ η,
      ((D ξ η).apply Γ (C.Θ η ξ) *
        (1 - Φ (ν (C.G.dilate ε⁻¹ (C.Θ η ξ))))) * ψ η)
      (𝓝[>] (0 : ℝ))
      (𝓝 (H1.principalValueConvolution C.G ν ((D ξ ξ).apply Γ)
        (C.reflectedTransport ξ ψ ∘ C.G.inv) 0 +
        ∫ η, ((D ξ η).apply Γ (C.Θ η ξ) - (D ξ ξ).apply Γ (C.Θ η ξ)) * ψ η)) := by
  have hc : ContinuousOn ((D ξ ξ).apply Γ) {(0 : Fin (n + m) → ℝ)}ᶜ :=
    ((F.contDiffOn_kernelUncurry hΓ).comp
      (contDiffOn_const.prodMk (contDiffOn_const.prodMk contDiffOn_id))
      (fun _ hu => hu)).continuousOn
  have hh : ∀ t : ℝ, 0 < t → ∀ u, u ≠ 0 →
      (D ξ ξ).apply Γ (C.G.dilate t u) =
        t ^ (-(C.G.homogeneousDimension : ℝ)) * (D ξ ξ).apply Γ u := by
    intro t ht u hu
    simpa only [Nat.cast_zero, zero_sub, ← Real.rpow_intCast, Int.cast_neg, Int.cast_natCast]
      using F.apply_dilate hΓ hhom ξ ξ ht hu
  have hcancel := H1.vanishingShellIntegrals_homogeneousDerivative C.G (D ξ ξ)
    (by norm_num : (0 : ℝ) < 2) (F.homogeneous ξ ξ) hν hΓ.continuousOn
    (fun α _ => hΓ.of_le (by simp)) hhom
  have htF := tendsto_radialCritical_inputChart hξ hν hc hh hcancel Φ hΦ hr hrR hone hout hb ψ
  have hiE := integrable_criticalFamily_freezingError_test F Γ hΓ hhom hξ ψ
  have hzE : ∀ η, η ∉ C.U →
      ((D ξ η).apply Γ (C.Θ η ξ) - (D ξ ξ).apply Γ (C.Θ η ξ)) * ψ η = 0 := by
    intro η hη
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hη (ψ.tsupport_subset ht)), mul_zero]
  have htE := tendsto_integrableChart_radialCutoff hξ hν hiE hzE Φ hΦ
    (hr.trans hrR) hout hb
  have ht := htF.add htE
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  let θ := fun u => 1 - Φ (ν (C.G.dilate ε⁻¹ u))
  have hcθ : Continuous θ := continuous_const.sub
    (hΦ.comp (hν.1.comp (G2.continuous_dilate C.G ε⁻¹)))
  have heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 0 := by
    have hzν : ν (C.G.dilate ε⁻¹ (0 : Fin (n + m) → ℝ)) = 0 := by
      rw [G2.dilate_zero, (hν.2.2.1 0).mpr rfl]
    have he : ∀ᶠ u in 𝓝 (0 : Fin (n + m) → ℝ), ν (C.G.dilate ε⁻¹ u) < r :=
      (hν.1.comp (G2.continuous_dilate C.G ε⁻¹)).continuousAt.eventually
      (gt_mem_nhds (by simpa only [Function.comp_apply, hzν] using hr))
    filter_upwards [he] with u hu
    simp only [θ, hone _ hu, sub_self]
  have hg := H1.continuous_puncturedKernel_mul_cutoff hc hcθ heθ
  have hiF := (integrableOn_integral_comp_theta_mul_test hξ
    ((hg.comp continuous_neg).continuousOn.locallyIntegrableOn (C.e ξ).open_target.measurableSet) ψ).1
  have hiF' : IntegrableOn (fun η =>
      ((D ξ ξ).apply Γ (C.Θ η ξ) * θ (C.Θ η ξ)) * ψ η) C.U := by
    apply hiF.congr (ae_restrict_of_ae (ae_of_all _ (fun η => ?_)))
    by_cases hη : η ∈ C.U
    · simp only [Function.comp_apply, C.theta_antisymm ξ hξ η hη]
    · simp only [image_eq_zero_of_notMem_tsupport (fun ht => hη (ψ.tsupport_subset ht)), mul_zero]
  have hcη : ContinuousOn (fun η => θ (C.Θ η ξ)) C.U :=
    hcθ.comp_continuousOn (C.contDiffOn_Θ_fst hξ).continuousOn
  have hiE' : IntegrableOn (fun η => θ (C.Θ η ξ) *
      (((D ξ η).apply Γ (C.Θ η ξ) - (D ξ ξ).apply Γ (C.Θ η ξ)) * ψ η)) C.U :=
    hiE.integrableOn.bdd_mul (c := 2) (hcη.aestronglyMeasurable C.isOpen_U.measurableSet)
      (ae_of_all _ (fun η => by
        change ‖(1 : ℝ) - Φ (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))‖ ≤ 2
        have hn := norm_sub_le (1 : ℝ) (Φ (ν (C.G.dilate ε⁻¹ (C.Θ η ξ))))
        have hb' := hb (C.G.dilate ε⁻¹ (C.Θ η ξ))
        norm_num only [norm_one] at hn
        linarith))
  have heE : (∫ η, θ (C.Θ η ξ) *
      (((D ξ η).apply Γ (C.Θ η ξ) - (D ξ ξ).apply Γ (C.Θ η ξ)) * ψ η)) =
      ∫ η in C.U, θ (C.Θ η ξ) *
      (((D ξ η).apply Γ (C.Θ η ξ) - (D ξ ξ).apply Γ (C.Θ η ξ)) * ψ η) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun η hη => by rw [hzE η hη, mul_zero])).symm
  have heV : (∫ η in C.U, (D ξ η).apply Γ (C.Θ η ξ) * θ (C.Θ η ξ) * ψ η) =
      ∫ η, (D ξ η).apply Γ (C.Θ η ξ) * θ (C.Θ η ξ) * ψ η :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun η hη => by
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hη (ψ.tsupport_subset ht))]
      simp only [mul_zero])
  change (∫ η in C.U, (D ξ ξ).apply Γ (C.Θ η ξ) * θ (C.Θ η ξ) * ψ η) +
      (∫ η, θ (C.Θ η ξ) *
        (((D ξ η).apply Γ (C.Θ η ξ) - (D ξ ξ).apply Γ (C.Θ η ξ)) * ψ η)) = _
  rw [heE, ← integral_add hiF' hiE', ← heV]
  apply integral_congr_ae
  exact ae_of_all _ (fun η => by ring)

end RothschildStein.P1.LiftedChart

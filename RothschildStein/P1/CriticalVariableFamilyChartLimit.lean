-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.CriticalFamilyFreezingIntegrability
public import RothschildStein.P1.IntegrableChartTruncationLimit
public import RothschildStein.P1.AmbientCriticalInputChart
public import RothschildStein.H1.HomogeneousDerivativeCancellation

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

/-- The actual variable critical family has an
ambient chart principal value: the model pairing at the fixed endpoint plus the
absolutely integrable endpoint-freezing error. -/
theorem criticalVariableFamily_inputChart_principalValue
    (F : SplitFamily C.G D) (Γ : (Fin (n + m) → ℝ) → ℝ)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      Γ (C.G.dilate r u) = r ^ (2 - (C.G.homogeneousDimension : ℝ)) * Γ u)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    (∀ ε : ℝ, 0 < ε → IntegrableOn
      (fun η => (D ξ η).apply Γ (C.Θ η ξ) * ψ η)
      {η | ε < ν (C.Θ η ξ)} volume) ∧
    Tendsto (fun ε : ℝ => ∫ η in {η | ε < ν (C.Θ η ξ)},
      (D ξ η).apply Γ (C.Θ η ξ) * ψ η) (𝓝[>] (0 : ℝ))
      (𝓝 (H1.principalValueConvolution C.G ν ((D ξ ξ).apply Γ)
        (C.reflectedTransport ξ ψ ∘ C.G.inv) 0 +
        ∫ η, ((D ξ η).apply Γ (C.Θ η ξ) - (D ξ ξ).apply Γ (C.Θ η ξ)) * ψ η)) := by
  have hc : ContinuousOn ((D ξ ξ).apply Γ) {(0 : Fin (n + m) → ℝ)}ᶜ :=
    ((F.contDiffOn_kernelUncurry hΓ).comp
      (contDiffOn_const.prodMk (contDiffOn_const.prodMk contDiffOn_id))
      (fun _ hu => hu)).continuousOn
  have hh : ∀ r : ℝ, 0 < r → ∀ u, u ≠ 0 →
      (D ξ ξ).apply Γ (C.G.dilate r u) =
        r ^ (-(C.G.homogeneousDimension : ℝ)) * (D ξ ξ).apply Γ u := by
    intro r hr u hu
    have hs := F.apply_dilate hΓ hhom ξ ξ hr hu
    simpa only [Nat.cast_zero, zero_sub, ← Real.rpow_intCast, Int.cast_neg, Int.cast_natCast] using hs
  have hcancel := H1.vanishingShellIntegrals_homogeneousDerivative C.G (D ξ ξ)
    (by norm_num : (0 : ℝ) < 2) (F.homogeneous ξ ξ) hν hΓ.continuousOn
    (fun α _ => hΓ.of_le (by simp)) hhom
  obtain ⟨hiFrozen, htFrozen⟩ := criticalInputChart_principalValue_ambient hξ hν hc hh hcancel ψ
  have hiError := integrable_criticalFamily_freezingError_test F Γ hΓ hhom hξ ψ
  have htError := tendsto_integrableChart_truncation hξ hν hiError (fun η hη => by
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hη (ψ.tsupport_subset ht)), mul_zero])
  refine ⟨?_, ?_⟩
  · intro ε hε
    have hi : IntegrableOn (fun η =>
        (D ξ ξ).apply Γ (C.Θ η ξ) * ψ η +
        ((D ξ η).apply Γ (C.Θ η ξ) - (D ξ ξ).apply Γ (C.Θ η ξ)) * ψ η)
        {η | ε < ν (C.Θ η ξ)} volume := (hiFrozen ε hε).add hiError.integrableOn
    exact hi.congr (ae_of_all _ (fun η => by ring))
  · refine (htFrozen.add htError).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← integral_add (hiFrozen ε hε) hiError.integrableOn]
    apply integral_congr_ae
    exact ae_of_all _ (fun η => by ring)

end RothschildStein.P1.LiftedChart

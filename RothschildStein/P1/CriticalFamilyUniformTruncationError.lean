-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FrozenFamilyUniformTruncationError
public import RothschildStein.P1.FreezingErrorUniformSmallBall
public import RothschildStein.P1.InputFamilyTruncationDifference
public import RothschildStein.P1.AmbientFrozenInputTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}
  {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}

/-- The complete moving-endpoint critical family
has a uniform O(ε) error to its actual prescribed sharp principal value
on compact center patches. Neither the endpoint nor the density is fixed in advance. -/
theorem exists_criticalFamily_uniform_truncation_error_bound
    (F : SplitFamily C.G D) (Γ : (Fin (n + m) → ℝ) → ℝ)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      Γ (C.G.dilate r u) = r ^ (2 - (C.G.homogeneousDimension : ℝ)) * Γ u)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ r A : ℝ, 0 < r ∧ 0 ≤ A ∧ ∀ ξ ∈ K, ∀ ε : ℝ, 0 < ε → ε < r →
      ‖(∫ η in {η | ε < ν (C.Θ η ξ)}, (D ξ η).apply Γ (C.Θ η ξ) * ψ η) -
        limUnder (𝓝[>] (0 : ℝ)) (fun ε : ℝ => ∫ η in {η | ε < ν (C.Θ η ξ)},
          (D ξ η).apply Γ (C.Θ η ξ) * ψ η)‖ ≤ A * ε := by
  obtain ⟨AF, hAF, hbF⟩ := C.exists_frozenFamily_uniform_truncation_error_bound
    F Γ hΓ hhom hν ψ hK hKU
  obtain ⟨rE, AE, hrE, hAE, hbE⟩ := C.exists_freezingError_uniform_smallBall_bound
    F Γ hΓ hhom hν ψ hK hKU
  refine ⟨min 1 rE, AF + AE, lt_min zero_lt_one hrE, add_nonneg hAF hAE, ?_⟩
  intro ξ hξ ε hε hεr
  have hε1 : ε < 1 := hεr.trans_le (min_le_left _ _)
  have hεE : ε ≤ rE := (hεr.trans_le (min_le_right _ _)).le
  let E := fun ζ η u => (D ζ η).apply Γ u - (D ζ ζ).apply Γ u
  have hiE := C.integrable_criticalFamily_freezingError_test F Γ hΓ hhom (hKU hξ) ψ
  have heE := C.inputFamily_truncation_sub_integral (hKU hξ) ν hν.1 E ψ hiE ε
  have hbErr : ‖(∫ η in {η | ε < ν (C.Θ η ξ)}, E ξ η (C.Θ η ξ) * ψ η) -
      (∫ η, E ξ η (C.Θ η ξ) * ψ η)‖ ≤ AE * ε := by
    rw [heE, norm_neg]
    exact hbE ξ hξ ε hε hεE
  have hc : ContinuousOn ((D ξ ξ).apply Γ) {(0 : Fin (n + m) → ℝ)}ᶜ :=
    ((F.contDiffOn_kernelUncurry hΓ).comp
      (contDiffOn_const.prodMk (contDiffOn_const.prodMk contDiffOn_id)) (fun _ hu => hu)).continuousOn
  have hh : ∀ r : ℝ, 0 < r → ∀ u, u ≠ 0 → (D ξ ξ).apply Γ (C.G.dilate r u) =
      r ^ (-(C.G.homogeneousDimension : ℝ)) * (D ξ ξ).apply Γ u := by
    intro r hr u hu
    simpa only [Nat.cast_zero, zero_sub, ← Real.rpow_intCast, Int.cast_neg, Int.cast_natCast]
      using F.apply_dilate hΓ hhom ξ ξ hr hu
  have hcancel := H1.vanishingShellIntegrals_homogeneousDerivative C.G (D ξ ξ)
    (by norm_num : (0 : ℝ) < 2) (F.homogeneous ξ ξ) hν hΓ.continuousOn
    (fun α _ => hΓ.of_le (by simp)) hhom
  have hiF := (C.criticalInputChart_principalValue_ambient (hKU hξ) hν hc hh hcancel ψ).1 ε hε
  have heFull : (∫ η in {η | ε < ν (C.Θ η ξ)}, (D ξ η).apply Γ (C.Θ η ξ) * ψ η) =
      (∫ η in {η | ε < ν (C.Θ η ξ)}, (D ξ ξ).apply Γ (C.Θ η ξ) * ψ η) +
      ∫ η in {η | ε < ν (C.Θ η ξ)}, E ξ η (C.Θ η ξ) * ψ η := by
    rw [← integral_add hiF hiE.integrableOn]
    exact integral_congr_ae (Eventually.of_forall (fun η => by dsimp only [E]; ring))
  have hePV := (C.criticalVariableFamily_inputChart_principalValue F Γ hΓ hhom (hKU hξ) hν ψ).2.limUnder_eq
  rw [heFull, hePV, C.integral_sharp_inputChart_ambient (hKU hξ) ν ((D ξ ξ).apply Γ) hν.1 ε ψ]
  have heAlg : (∫ u in {u | ε < ν u}, (D ξ ξ).apply Γ u * C.reflectedTransport ξ ψ u) +
      (∫ η in {η | ε < ν (C.Θ η ξ)}, E ξ η (C.Θ η ξ) * ψ η) -
      (H1.principalValueConvolution C.G ν ((D ξ ξ).apply Γ) (C.reflectedTransport ξ ψ ∘ C.G.inv) 0 +
        ∫ η, E ξ η (C.Θ η ξ) * ψ η) =
      ((∫ u in {u | ε < ν u}, (D ξ ξ).apply Γ u * C.reflectedTransport ξ ψ u) -
        H1.principalValueConvolution C.G ν ((D ξ ξ).apply Γ) (C.reflectedTransport ξ ψ ∘ C.G.inv) 0) +
      ((∫ η in {η | ε < ν (C.Θ η ξ)}, E ξ η (C.Θ η ξ) * ψ η) -
        ∫ η, E ξ η (C.Θ η ξ) * ψ η) := by ring
  change ‖_ + _ - (_ + ∫ η, E ξ η (C.Θ η ξ) * ψ η)‖ ≤ _
  rw [heAlg]
  exact (norm_add_le _ _).trans ((add_le_add (hbF ξ hξ ε hε hε1) hbErr).trans_eq (by ring))

end RothschildStein.P1.LiftedChart

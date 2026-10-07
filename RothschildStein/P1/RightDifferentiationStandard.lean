-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeInputBoundaryLimit
public import RothschildStein.P1.InputDifferentiatedOperator
public import RothschildStein.P1.TypeOperatorRadialLimit
public import RothschildStein.P1.TypeOperatorOutsideSupport
public import RothschildStein.P1.TypeCalculusStatements

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- The constructed differentiated operator
acts exactly as T applied to the actual input field derivative. -/
theorem inputDifferentiatedOperator_apply {lam : ℕ}
    (hF : C.IsStandardFrame F H K hQ) (T : TypeOperator F lam) (i : Fin k)
    (hw : (w i : ℕ) ≤ lam)
    (hXt : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl j) (F.V : Set (Fin (n + m) → ℝ)))
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    T.apply (S.wordDerivativeTest F.V C.Xl hXt [i] φ) =
      (C.inputDifferentiatedOperator hF T i hw).apply φ := by
  let rsRightDiffFinNonempty : Nonempty (Fin (n + m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  let S₁ := C.inputDifferentiatedOperator hF T i hw
  let d : TypeDecomposition F lam 1 T.kernel := Classical.choice (T.isType 1)
  let dφ := S.wordDerivativeTest F.V C.Xl hXt [i] φ
  have hlam : lam ≠ 0 := by have hp := (w i).pos; omega
  have hμ (ξ : Fin (n + m) → ℝ) : T.mult ξ = 0 := by
    simpa only [Pi.zero_apply] using congrFun (T.mult_eq_zero hlam) ξ
  funext ξ
  by_cases hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ))
  · let L := fun ε : ℝ => ∫ η,
      (1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ η ξ)))) * (T.kernel ξ η * dφ η)
    let R := fun ε : ℝ => ∫ η,
      (1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ η ξ)))) * (S₁.kernel ξ η * φ η)
    let B := fun ε : ℝ => ∫ η, -(fieldDerivative (C.Xl i)
      (fun ζ => 1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ ζ ξ)))) η) *
        T.kernel ξ η * φ η
    have htL : Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 (T.apply dφ ξ)) := by
      simpa only [hμ ξ, zero_mul, sub_zero] using
        C.typeOperator_tendsto_radialIntegral hF T dφ hξ
    have htR : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 (S₁.apply φ ξ - S₁.mult ξ * φ ξ)) :=
      C.typeOperator_tendsto_radialIntegral hF S₁ φ hξ
    have htB : Tendsto B (𝓝[>] (0 : ℝ)) (𝓝 (S₁.mult ξ * φ ξ)) :=
      C.tendsto_typeInput_boundary_multiplier hF T.isType d i hw hξ φ
    have he (ε : ℝ) : L ε = R ε + B ε := by
      have hiR := C.isTypeKernel_integrable_inputCutoff hF.lifted S₁.isType hξ
        (radialGaugeCutoff_contDiff H.norm.gauge hF.norm_smooth)
        (radialGaugeCutoff_eventually_one H.norm.gauge) ε φ
      have hiB := C.isTypeKernel_integrable_inputBoundary hF.lifted T.isType hξ i
        (radialGaugeCutoff_contDiff H.norm.gauge hF.norm_smooth)
        (radialGaugeCutoff_eventually_one H.norm.gauge) ε φ
      have hiR' : Integrable (fun η =>
          (1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ η ξ)))) *
            (S₁.kernel ξ η * φ η)) :=
        hiR.congr (Eventually.of_forall (fun η => by ring))
      have hfinite := C.isTypeKernel_finite_inputCutoff_adjoint_identity hF.lifted
        T.isType hξ i (radialGaugeCutoff_contDiff H.norm.gauge hF.norm_smooth)
        (radialGaugeCutoff_eventually_one H.norm.gauge) ε φ
      have heL : L ε = ∫ η, ((1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ η ξ)))) *
          T.kernel ξ η) * fieldDerivative (C.Xl i) φ η := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro η
        change (1 - _) * (T.kernel ξ η * fieldDerivative (C.Xl i) φ η) = _
        ring
      rw [heL, hfinite]
      change _ = (∫ η, (1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ η ξ)))) *
          (S₁.kernel ξ η * φ η)) +
        ∫ η, -(fieldDerivative (C.Xl i)
          (fun ζ => 1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ ζ ξ)))) η) *
            T.kernel ξ η * φ η
      rw [← integral_add hiR' hiB]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro η
      change ((1 - _) * cutoffInputTranspose F (C.Xl i) T.kernel ξ η - _) * φ η =
        (1 - _) * (cutoffInputTranspose F (C.Xl i) T.kernel ξ η * φ η) + _
      ring
    have ht := htR.add htB
    rw [sub_add_cancel] at ht
    have htS : Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 (S₁.apply φ ξ)) :=
      ht.congr' (Eventually.of_forall (fun ε => (he ε).symm))
    exact tendsto_nhds_unique htL htS
  · rw [T.apply_eq_zero_outside dφ hξ, S₁.apply_eq_zero_outside φ hξ]

/-- Full RightDifferentiation on every standard frame, with no conditional
endpoint-limit or operator-identity premise. -/
theorem rightDifferentiation_standard (hF : C.IsStandardFrame F H K hQ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ))) :
    RightDifferentiation F w C.Xl hXt := by
  intro lam T i hw
  exact ⟨C.inputDifferentiatedOperator hF T i hw,
    C.inputDifferentiatedOperator_apply hF T i hw hXt⟩

end RothschildStein.P1.LiftedChart

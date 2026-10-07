-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RightParametrixKernel

/-!
# Fubini for the right parametrix kernels

A kernel `κ(ξ, η)` that is continuous on the off-diagonal set of `C.U × C.U` is a.e. strongly
measurable for the product of the restrictions of Lebesgue measure to `C.U` (the diagonal is null);
if `∫⁻_{ξ ∈ Kt} ‖κ(ξ, η)‖ₑ dξ ≤ M < ⊤` for `η ∈ Kw` (compact sets), then `t(ξ) κ(ξ, η) w(η)` is
integrable on the product for bounded continuous `t, w` supported in `Kt, Kw`, and the order of
integration can be exchanged (`integral_integral_swap`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P1

section Product

variable {N : ℕ}

/-- The diagonal of `ℝ^N × ℝ^N` is null (`N ≥ 1`). -/
theorem volume_prod_diagonal_eq_zero [NeZero N] :
    (volume : Measure (Fin N → ℝ)).prod (volume : Measure (Fin N → ℝ))
      {p : (Fin N → ℝ) × (Fin N → ℝ) | p.1 = p.2} = 0 := by
  rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
  simp

/-- A function continuous on `{(ξ, η) ∈ U × U | ξ ≠ η}` (`U` open) is a.e. strongly
measurable for the product of the restrictions of Lebesgue measure to `U`. -/
theorem aestronglyMeasurable_prod_of_continuousOn [NeZero N] {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    {f : (Fin N → ℝ) × (Fin N → ℝ) → ℝ}
    (hf : ContinuousOn f {p | p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 ≠ p.2}) :
    AEStronglyMeasurable f ((volume.restrict U).prod (volume.restrict U)) := by
  have hopen : IsOpen {p : (Fin N → ℝ) × (Fin N → ℝ) | p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 ≠ p.2} :=
    (hU.preimage continuous_fst).inter ((hU.preimage continuous_snd).inter
      (isOpen_ne_fun continuous_fst continuous_snd))
  rw [Measure.prod_restrict]
  have hae : ({p : (Fin N → ℝ) × (Fin N → ℝ) | p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 ≠ p.2} :
      Set ((Fin N → ℝ) × (Fin N → ℝ))) =ᵐ[(volume : Measure (Fin N → ℝ)).prod volume] U ×ˢ U := by
    have h1 : (U ×ˢ U \ {p : (Fin N → ℝ) × (Fin N → ℝ) | p.1 = p.2} :
        Set ((Fin N → ℝ) × (Fin N → ℝ))) =ᵐ[(volume : Measure (Fin N → ℝ)).prod volume] U ×ˢ U :=
      sdiff_null_ae_eq_self volume_prod_diagonal_eq_zero
    refine Filter.EventuallyEq.trans (Filter.EventuallyEq.of_eq ?_) h1
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_prod]
    tauto
  rw [← Measure.restrict_congr_set hae]
  exact hf.aestronglyMeasurable hopen.measurableSet

/-- Integrability on the product of `t(ξ) κ(ξ, η) w(η)` from a uniform bound of the
lower integrals of `κ(·, η)` over the support `Kt` of `t`, for `η` in the support `Kw` of `w`. -/
theorem integrable_prod_of_mass_bound [NeZero N] {U Kt Kw : Set (Fin N → ℝ)}
    (hKtU : Kt ⊆ U) (hKt : MeasurableSet Kt) (hKw : MeasurableSet Kw) (hKwfin : volume Kw < ⊤)
    {κ : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} {t w : (Fin N → ℝ) → ℝ} {Bt Bw : ℝ}
    (hκ : AEStronglyMeasurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => κ p.1 p.2)
      ((volume.restrict U).prod (volume.restrict U)))
    (ht : AEStronglyMeasurable t (volume.restrict U)) (hw : AEStronglyMeasurable w (volume.restrict U))
    (htB : ∀ ξ ∈ Kt, |t ξ| ≤ Bt) (hwB : ∀ η ∈ Kw, |w η| ≤ Bw)
    (ht0 : ∀ ξ ∉ Kt, t ξ = 0) (hw0 : ∀ η ∉ Kw, w η = 0) {M : ℝ≥0∞} (hM : M < ⊤)
    (hmass : ∀ η ∈ Kw, ∫⁻ ξ in Kt, ‖κ ξ η‖ₑ ≤ M) :
    Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => t p.1 * κ p.1 p.2 * w p.2)
      ((volume.restrict U).prod (volume.restrict U)) := by
  set μ : Measure (Fin N → ℝ) := volume.restrict U with hμ
  have h1 : AEStronglyMeasurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => t p.1) (μ.prod μ) := ht.comp_fst
  have h2 : AEStronglyMeasurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => w p.2) (μ.prod μ) := hw.comp_snd
  have hmeas : AEStronglyMeasurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      t p.1 * κ p.1 p.2 * w p.2) (μ.prod μ) := (h1.mul hκ).mul h2
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_prod_symm _ hmeas.enorm]
  -- bound the inner integral for each `η`
  have hinner : ∀ η : Fin N → ℝ, ∫⁻ ξ, ‖t ξ * κ ξ η * w η‖ₑ ∂μ ≤
      Kw.indicator (fun _ => ENNReal.ofReal Bw * (ENNReal.ofReal Bt * M)) η := by
    intro η
    by_cases hη : η ∈ Kw
    · rw [Set.indicator_of_mem hη]
      have h1 : ∀ ξ, ‖t ξ * κ ξ η * w η‖ₑ ≤
          Kt.indicator (fun ξ => ENNReal.ofReal Bw * (ENNReal.ofReal Bt * ‖κ ξ η‖ₑ)) ξ := by
        intro ξ
        by_cases hξ : ξ ∈ Kt
        · rw [Set.indicator_of_mem hξ, enorm_mul, enorm_mul]
          have e1 : ‖t ξ‖ₑ ≤ ENNReal.ofReal Bt := by
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal (htB ξ hξ)
          have e2 : ‖w η‖ₑ ≤ ENNReal.ofReal Bw := by
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal (hwB η hη)
          calc ‖t ξ‖ₑ * ‖κ ξ η‖ₑ * ‖w η‖ₑ ≤ ENNReal.ofReal Bt * ‖κ ξ η‖ₑ * ENNReal.ofReal Bw := by
                gcongr
            _ = ENNReal.ofReal Bw * (ENNReal.ofReal Bt * ‖κ ξ η‖ₑ) := by ring
        · rw [Set.indicator_of_notMem hξ, ht0 ξ hξ]
          simp
      calc ∫⁻ ξ, ‖t ξ * κ ξ η * w η‖ₑ ∂μ
          ≤ ∫⁻ ξ, Kt.indicator (fun ξ => ENNReal.ofReal Bw * (ENNReal.ofReal Bt * ‖κ ξ η‖ₑ)) ξ ∂μ :=
            lintegral_mono h1
        _ = ∫⁻ ξ in Kt, ENNReal.ofReal Bw * (ENNReal.ofReal Bt * ‖κ ξ η‖ₑ) ∂μ :=
            lintegral_indicator hKt _
        _ = ∫⁻ ξ in Kt, ENNReal.ofReal Bw * (ENNReal.ofReal Bt * ‖κ ξ η‖ₑ) := by
            rw [hμ, Measure.restrict_restrict hKt, inter_eq_left.2 hKtU]
        _ = ENNReal.ofReal Bw * (ENNReal.ofReal Bt * ∫⁻ ξ in Kt, ‖κ ξ η‖ₑ) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal Bw * (ENNReal.ofReal Bt * M) := by gcongr; exact hmass η hη
    · rw [Set.indicator_of_notMem hη, hw0 η hη]
      simp
  calc ∫⁻ η, ∫⁻ ξ, ‖t ξ * κ ξ η * w η‖ₑ ∂μ ∂μ
      ≤ ∫⁻ η, Kw.indicator (fun _ => ENNReal.ofReal Bw * (ENNReal.ofReal Bt * M)) η ∂μ :=
        lintegral_mono hinner
    _ = ∫⁻ η in Kw, ENNReal.ofReal Bw * (ENNReal.ofReal Bt * M) ∂μ :=
        lintegral_indicator hKw _
    _ = ENNReal.ofReal Bw * (ENNReal.ofReal Bt * M) * μ Kw := setLIntegral_const _ _
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM)) ?_
        exact lt_of_le_of_lt ((Measure.restrict_le_self : volume.restrict U ≤ volume) Kw) hKwfin

end Product

end RothschildStein.P1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.NormTransferFubini

/-!
# Fiber integration in Lp spaces

For a lifted open set `A` over a base set `V`, with fiber volumes bounded above by `cup` on the
whole base and below by `clow` on a smaller set `W ⊆ V`, Tonelli gives the two-sided `L^p`
comparison of `f` and `f ∘ π` (BB pp. 584–585, Thms 11.40–11.41, (11.68)):

* `∫_A |f ∘ π|^q ≤ cup ∫_V |f|^q` and `clow ∫_W |f|^q ≤ ∫_A |f ∘ π|^q`;
* hence `‖f ∘ π‖_{L^p(A)} ≤ cup^{1/p} ‖f‖_{L^p(V)}` and
  `clow^{1/p} ‖f‖_{L^p(W)} ≤ ‖f ∘ π‖_{L^p(A)}` for `1 ≤ p < ∞`;
* for `p = ∞`, `‖f ∘ π‖_{L^∞(A)} ≤ ‖f‖_{L^∞(V)}` and `‖f‖_{L^∞(W)} ≤ ‖f ∘ π‖_{L^∞(A)}`
  when `clow > 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace RothschildStein.P2
variable {n m : ℕ}

/-- The fiber data of a lifted set `A` over a base set `V`: measurable sets, projection
`π (A) ⊆ V`, the upper fiber bound `cup` on all of `ℝⁿ`, and the lower fiber bound `clow` on
the smaller set `W ⊆ V` (the two fiber bounds of BB p. 584). -/
structure FiberBounds (A : Set (Fin (n + m) → ℝ)) (V W : Set (Fin n → ℝ)) (cup clow : ℝ) :
    Prop where
  cup_nonneg : 0 ≤ cup
  clow_nonneg : 0 ≤ clow
  measurableSet_A : MeasurableSet A
  measurableSet_V : MeasurableSet V
  measurableSet_W : MeasurableSet W
  subset : W ⊆ V
  proj : ∀ ξ ∈ A, basePoint ξ ∈ V
  upper : ∀ z, fiberVolume A z ≤ ENNReal.ofReal cup
  lower : ∀ z ∈ W, ENNReal.ofReal clow ≤ fiberVolume A z

namespace FiberBounds

variable {A : Set (Fin (n + m) → ℝ)} {V W : Set (Fin n → ℝ)} {cup clow : ℝ}

/-- Upper `L^q` bound, in lintegral form. -/
theorem lintegral_le (h : FiberBounds A V W cup clow) {F : (Fin n → ℝ) → ℝ≥0∞}
    (hF : AEMeasurable F (volume.restrict V)) :
    ∫⁻ ξ in A, F (basePoint ξ) ≤ ENNReal.ofReal cup * ∫⁻ x in V, F x := by
  have hFv : AEMeasurable (V.indicator F) volume :=
    (aemeasurable_indicator_iff h.measurableSet_V).2 hF
  have h1 : ∫⁻ ξ in A, F (basePoint ξ) = ∫⁻ ξ in A, V.indicator F (basePoint ξ) := by
    apply setLIntegral_congr_fun h.measurableSet_A
    intro ξ hξ
    simp [h.proj ξ hξ]
  rw [h1, lintegral_comp_basePoint h.measurableSet_A hFv, ← lintegral_indicator h.measurableSet_V,
    ← lintegral_const_mul'' _ hFv]
  apply lintegral_mono
  intro x
  dsimp only
  rw [mul_comm]
  exact mul_le_mul' (h.upper x) le_rfl

/-- Lower `L^q` bound, in lintegral form. -/
theorem le_lintegral (h : FiberBounds A V W cup clow) {F : (Fin n → ℝ) → ℝ≥0∞}
    (hF : AEMeasurable F (volume.restrict V)) :
    ENNReal.ofReal clow * ∫⁻ x in W, F x ≤ ∫⁻ ξ in A, F (basePoint ξ) := by
  have hFv : AEMeasurable (V.indicator F) volume :=
    (aemeasurable_indicator_iff h.measurableSet_V).2 hF
  have hFw : AEMeasurable (W.indicator F) volume :=
    (aemeasurable_indicator_iff h.measurableSet_W).2
      (hF.mono_measure (Measure.restrict_mono h.subset le_rfl))
  have h1 : ∫⁻ ξ in A, F (basePoint ξ) = ∫⁻ ξ in A, V.indicator F (basePoint ξ) := by
    apply setLIntegral_congr_fun h.measurableSet_A
    intro ξ hξ
    simp [h.proj ξ hξ]
  rw [h1, lintegral_comp_basePoint h.measurableSet_A hFv, ← lintegral_indicator h.measurableSet_W,
    ← lintegral_const_mul'' _ hFw]
  apply lintegral_mono
  intro x
  dsimp only
  by_cases hx : x ∈ W
  · simp only [indicator_of_mem hx, indicator_of_mem (h.subset hx)]
    rw [mul_comm]
    exact mul_le_mul' le_rfl (h.lower x hx)
  · simp [hx]

/-- upper `L^p` comparison, `1 ≤ p < ∞`. -/
theorem eLpNorm_comp_le (h : FiberBounds A V W cup clow) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    {f : (Fin n → ℝ) → ℝ} (hf : AEStronglyMeasurable f (volume.restrict V)) :
    eLpNorm (fun ξ => f (basePoint ξ)) p (volume.restrict A) ≤
      ENNReal.ofReal (cup ^ (1 / p.toReal)) * eLpNorm f p (volume.restrict V) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hfA := aestronglyMeasurable_comp_basePoint h.measurableSet_A h.measurableSet_V h.proj hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hfA,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf]
  have hF : AEMeasurable (fun x => ‖f x‖ₑ ^ p.toReal) (volume.restrict V) :=
    hf.enorm.pow_const _
  have hle := h.lintegral_le hF
  calc (∫⁻ ξ in A, ‖f (basePoint ξ)‖ₑ ^ p.toReal) ^ (1 / p.toReal)
      ≤ (ENNReal.ofReal cup * ∫⁻ x in V, ‖f x‖ₑ ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow hle (by positivity)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
        congr 1
        rw [ENNReal.ofReal_rpow_of_nonneg h.cup_nonneg (by positivity)]

/-- lower `L^p` comparison, `1 ≤ p < ∞`. -/
theorem le_eLpNorm_comp (h : FiberBounds A V W cup clow) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    {f : (Fin n → ℝ) → ℝ} (hf : AEStronglyMeasurable f (volume.restrict V)) :
    ENNReal.ofReal (clow ^ (1 / p.toReal)) * eLpNorm f p (volume.restrict W) ≤
      eLpNorm (fun ξ => f (basePoint ξ)) p (volume.restrict A) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hfA := aestronglyMeasurable_comp_basePoint h.measurableSet_A h.measurableSet_V h.proj hf
  have hfW : AEStronglyMeasurable f (volume.restrict W) :=
    hf.mono_measure (Measure.restrict_mono h.subset le_rfl)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hfA,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hfW]
  have hF : AEMeasurable (fun x => ‖f x‖ₑ ^ p.toReal) (volume.restrict V) :=
    hf.enorm.pow_const _
  have hle := h.le_lintegral hF
  calc ENNReal.ofReal (clow ^ (1 / p.toReal)) * (∫⁻ x in W, ‖f x‖ₑ ^ p.toReal) ^ (1 / p.toReal)
      = (ENNReal.ofReal clow * ∫⁻ x in W, ‖f x‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.ofReal_rpow_of_nonneg h.clow_nonneg (by positivity)]
    _ ≤ _ := ENNReal.rpow_le_rpow hle (by positivity)

end FiberBounds

end RothschildStein.P2

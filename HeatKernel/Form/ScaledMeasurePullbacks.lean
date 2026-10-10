-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.GradientPullbacks
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linter

/-! # Continuous L² pullbacks with an explicit measure scaling factor -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HeatKernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {J : ℝ≥0∞}

/-- Pullback on L² under a map whose pushforward measure is a finite scalar multiple. -/
def scaledMeasurePullback (hT : Measurable T) (hmap : Measure.map T μ = J • μ) (hJ : J ≠ ⊤) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ T (⟨hT, hmap⟩ : MeasurePreserving T μ (J • μ))).toContinuousLinearMap.comp
    (Lp.LpToLpOfMeasureLeSMul hJ (le_rfl : J • μ ≤ J • μ))

/-- A scaled-measure pullback has its expected almost everywhere representative. -/
theorem scaledMeasurePullback_ae (hT : Measurable T) (hmap : Measure.map T μ = J • μ) (hJ : J ≠ ⊤)
    (f : Lp ℝ 2 μ) : scaledMeasurePullback hT hmap hJ f =ᵐ[μ] f ∘ T := by
  let hm : MeasurePreserving T μ (J • μ) := ⟨hT, hmap⟩
  exact (Lp.coeFn_compMeasurePreserving (Lp.LpToLpOfMeasureLeSMul hJ (le_rfl : J • μ ≤ J • μ) f) hm).trans
    (hm.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_LpToLpOfMeasureLeSMul hJ le_rfl f))

/-- The L² inner product scales by the pushforward measure factor. -/
theorem inner_scaledMeasurePullback (hT : MeasurableEmbedding T)
    (hmap : Measure.map T μ = J • μ) (hJ : J ≠ ⊤) (f g : Lp ℝ 2 μ) :
    inner ℝ (scaledMeasurePullback hT.measurable hmap hJ f)
      (scaledMeasurePullback hT.measurable hmap hJ g) = J.toReal * inner ℝ f g := by
  rw [L2.inner_def, L2.inner_def]
  have H : (fun x => inner ℝ (scaledMeasurePullback hT.measurable hmap hJ f x)
      (scaledMeasurePullback hT.measurable hmap hJ g x)) =ᵐ[μ]
      (fun x => inner ℝ (f (T x)) (g (T x))) := by
    filter_upwards [scaledMeasurePullback_ae hT.measurable hmap hJ f,
      scaledMeasurePullback_ae hT.measurable hmap hJ g] with x hx hy
    rw [hx, hy]
    rfl
  rw [integral_congr_ae H,
    (⟨hT.measurable, hmap⟩ : MeasurePreserving T μ (J • μ)).integral_comp hT (fun x => inner ℝ (f x) (g x)),
    integral_smul_measure]
  rfl


end HeatKernel

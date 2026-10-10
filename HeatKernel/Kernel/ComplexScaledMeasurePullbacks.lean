-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linter

/-! # Complex L² pullbacks with an explicit measure scaling factor -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HeatKernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {J : ℝ≥0∞}

/-- Changing to a finite scalar multiple of the measure is complex linear on L². -/
def complexL2MeasureScale (hJ : J ≠ ⊤) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (J • μ) where
  toFun := Lp.LpToLpOfMeasureLeSMul hJ (le_rfl : J • μ ≤ J • μ)
  map_add' f g := (Lp.LpToLpOfMeasureLeSMul hJ (le_rfl : J • μ ≤ J • μ)).map_add f g
  map_smul' c f := by
    apply Lp.ext
    have hcoe := (Measure.smul_absolutelyContinuous (μ := μ) (c := J)).ae_eq (Lp.coeFn_smul c f)
    filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hJ (le_rfl : J • μ ≤ J • μ) (c • f),
      Lp.coeFn_LpToLpOfMeasureLeSMul hJ (le_rfl : J • μ ≤ J • μ) f,
      hcoe, Lp.coeFn_smul c (Lp.LpToLpOfMeasureLeSMul hJ (le_rfl : J • μ ≤ J • μ) f)]
      with x hcf hf hc hout
    simp only [Pi.smul_apply, smul_eq_mul] at hc hout
    change (Lp.LpToLpOfMeasureLeSMul hJ (le_rfl : J • μ ≤ J • μ) (c • f)) x =
      (c • Lp.LpToLpOfMeasureLeSMul hJ (le_rfl : J • μ ≤ J • μ) f) x
    rw [hout, hcf, hc, hf]
  cont := (Lp.LpToLpOfMeasureLeSMul hJ (le_rfl : J • μ ≤ J • μ)).continuous

/-- Pullback on L² under a map whose pushforward measure is a finite scalar multiple. -/
def complexScaledMeasurePullback (hT : Measurable T) (hmap : Measure.map T μ = J • μ) (hJ : J ≠ ⊤) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ T (⟨hT, hmap⟩ : MeasurePreserving T μ (J • μ))).toContinuousLinearMap.comp
    (complexL2MeasureScale hJ)

/-- A scaled-measure pullback has its expected almost everywhere representative. -/
theorem complexScaledMeasurePullback_ae (hT : Measurable T) (hmap : Measure.map T μ = J • μ) (hJ : J ≠ ⊤)
    (f : Lp ℂ 2 μ) : complexScaledMeasurePullback hT hmap hJ f =ᵐ[μ] f ∘ T := by
  let hm : MeasurePreserving T μ (J • μ) := ⟨hT, hmap⟩
  change Lp.compMeasurePreserving T hm
    (Lp.LpToLpOfMeasureLeSMul hJ (le_rfl : J • μ ≤ J • μ) f) =ᵐ[μ] f ∘ T
  exact (Lp.coeFn_compMeasurePreserving (Lp.LpToLpOfMeasureLeSMul hJ (le_rfl : J • μ ≤ J • μ) f) hm).trans
    (hm.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_LpToLpOfMeasureLeSMul hJ le_rfl f))

/-- The L² inner product scales by the pushforward measure factor. -/
theorem inner_complexScaledMeasurePullback (hT : MeasurableEmbedding T)
    (hmap : Measure.map T μ = J • μ) (hJ : J ≠ ⊤) (f g : Lp ℂ 2 μ) :
    inner ℂ (complexScaledMeasurePullback hT.measurable hmap hJ f)
      (complexScaledMeasurePullback hT.measurable hmap hJ g) = J.toReal • inner ℂ f g := by
  rw [L2.inner_def, L2.inner_def]
  have H : (fun x => inner ℂ (complexScaledMeasurePullback hT.measurable hmap hJ f x)
      (complexScaledMeasurePullback hT.measurable hmap hJ g x)) =ᵐ[μ]
      (fun x => inner ℂ (f (T x)) (g (T x))) := by
    filter_upwards [complexScaledMeasurePullback_ae hT.measurable hmap hJ f,
      complexScaledMeasurePullback_ae hT.measurable hmap hJ g] with x hx hy
    rw [hx, hy]
    rfl
  rw [integral_congr_ae H,
    (⟨hT.measurable, hmap⟩ : MeasurePreserving T μ (J • μ)).integral_comp hT (fun x => inner ℂ (f x) (g x)),
    integral_smul_measure]


end HeatKernel

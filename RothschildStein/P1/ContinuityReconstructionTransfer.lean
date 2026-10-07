-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.H2DataD

/-!
# Continuity: transfer between the carrier of the lifted chart and the ambient space

The H2 theorems live on the carrier `C.Carrier` (the chart domain `U` with the lifted control
metric and the measure `μ_c = comap val volume`); the continuity statements live on the ambient space
`ℝ^{n+m}` with Lebesgue measure. This module collects the transfer lemmas: a function of the
ambient space which vanishes outside `U` has the same integral, the same integrability and the same
`L^p` norms on `volume` as its pullback along `val` on `μ_c` (`val` is a measurable embedding
and `map val μ_c = volume.restrict U`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

namespace Carrier

/-- The image of the carrier measure under `val` is Lebesgue measure restricted to `U`. -/
theorem map_val_volume :
    Measure.map (val : C.Carrier → Fin (n + m) → ℝ) (volume : Measure C.Carrier) =
      volume.restrict C.U := by
  have hemb := Carrier.measurableEmbedding_val (C := C)
  have h : Measure.map (val : C.Carrier → Fin (n + m) → ℝ) (volume : Measure C.Carrier) =
      volume.restrict (range (Carrier.val : C.Carrier → Fin (n + m) → ℝ)) := by
    show Measure.map Carrier.val (Measure.comap Carrier.val volume) = _
    exact hemb.map_comap volume
  rw [h, range_val]

/-- A function of the ambient space which vanishes outside `U` has the same integral on
`volume` as its pullback to the carrier. -/
theorem integral_eq_comp_val (F : (Fin (n + m) → ℝ) → ℝ) (hF : ∀ ξ, ξ ∉ C.U → F ξ = 0) :
    ∫ ξ, F ξ = ∫ y, F y.val ∂(volume : Measure C.Carrier) := by
  have hemb := Carrier.measurableEmbedding_val (C := C)
  rw [← hemb.integral_map, map_val_volume,
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun ξ hξ => hF ξ hξ)]

/-- A function of the ambient space which vanishes outside `U` is integrable on `volume`
iff its pullback to the carrier is integrable. -/
theorem integrable_iff_comp_val (F : (Fin (n + m) → ℝ) → ℝ) (hF : ∀ ξ, ξ ∉ C.U → F ξ = 0) :
    Integrable F volume ↔ Integrable (fun y : C.Carrier => F y.val) volume := by
  have hemb := Carrier.measurableEmbedding_val (C := C)
  have hi := hemb.integrable_map_iff (g := F) (μ := (volume : Measure C.Carrier))
  rw [map_val_volume] at hi
  have hU : MeasurableSet C.U := C.isOpen_U.measurableSet
  change _ ↔ Integrable (F ∘ val) volume
  rw [← hi]
  constructor
  · intro h
    exact h.restrict
  · intro h
    have : Integrable (C.U.indicator F) volume := (integrable_indicator_iff hU).mpr h
    have he : C.U.indicator F = F := by
      funext ξ
      by_cases hξ : ξ ∈ C.U
      · simp [hξ]
      · simp [hξ, hF ξ hξ]
    rwa [he] at this

/-- `L^p` norms: for a measurable `S ⊆ U`, the `L^p(S)` norm of a function of the ambient
space is the `L^p(val⁻¹ S)` norm of its pullback to the carrier. -/
theorem eLpNorm_comp_val (F : (Fin (n + m) → ℝ) → ℝ) (p : ℝ≥0∞) {S : Set (Fin (n + m) → ℝ)}
    (hS : MeasurableSet S) (hSU : S ⊆ C.U) :
    eLpNorm (fun y : C.Carrier => F y.val) p
        ((volume : Measure C.Carrier).restrict (val ⁻¹' S)) =
      eLpNorm F p (volume.restrict S) := by
  have hemb := Carrier.measurableEmbedding_val (C := C)
  have h1 : Measure.map (val : C.Carrier → Fin (n + m) → ℝ)
      ((volume : Measure C.Carrier).restrict (val ⁻¹' S)) = volume.restrict S := by
    rw [← hemb.restrict_map, map_val_volume, Measure.restrict_restrict hS,
      inter_eq_left.mpr hSU]
  rw [← h1, hemb.eLpNorm_map_measure]
  rfl

/-- Almost-everywhere strong measurability transfers along `val` on `S ⊆ U`. -/
theorem aestronglyMeasurable_comp_val_iff (F : (Fin (n + m) → ℝ) → ℝ)
    {S : Set (Fin (n + m) → ℝ)} (hS : MeasurableSet S) (hSU : S ⊆ C.U) :
    AEStronglyMeasurable (fun y : C.Carrier => F y.val)
        ((volume : Measure C.Carrier).restrict (val ⁻¹' S)) ↔
      AEStronglyMeasurable F (volume.restrict S) := by
  have hemb := Carrier.measurableEmbedding_val (C := C)
  have h1 : Measure.map (val : C.Carrier → Fin (n + m) → ℝ)
      ((volume : Measure C.Carrier).restrict (val ⁻¹' S)) = volume.restrict S := by
    rw [← hemb.restrict_map, map_val_volume, Measure.restrict_restrict hS,
      inter_eq_left.mpr hSU]
  rw [← h1, hemb.aestronglyMeasurable_map_iff]
  rfl

end Carrier

end LiftedChart
end RothschildStein.P1

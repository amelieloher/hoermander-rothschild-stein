-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.TwoSpaceCoordinateMeasure

/-! # Exchange of the two spatial coordinate blocks

Swapping equal spatial blocks is a continuous linear involution preserving
Lebesgue measure and the positive-time domain.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- Exchange the two spatial blocks while retaining time. -/
def twoSpaceSwap (n : ℕ) :
    (Fin (1 + (n + n)) → ℝ) ≃L[ℝ] (Fin (1 + (n + n)) → ℝ) :=
  (timeTwoSpaceCoordinates n).trans
    (((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
      (ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) (Fin n → ℝ))).trans
        (timeTwoSpaceCoordinates n).symm)

/-- The coordinate description of exchange is ordinary spatial pair exchange. -/
theorem timeTwoSpaceCoordinates_twoSpaceSwap {n : ℕ} (z : Fin (1 + (n + n)) → ℝ) :
    timeTwoSpaceCoordinates n (twoSpaceSwap n z) =
      ((timeTwoSpaceCoordinates n z).1,
        ((timeTwoSpaceCoordinates n z).2.2, (timeTwoSpaceCoordinates n z).2.1)) := by
  change timeTwoSpaceCoordinates n ((timeTwoSpaceCoordinates n).symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- Spatial exchange retains the time coordinate. -/
theorem twoSpaceSwap_time {n : ℕ} (z : Fin (1 + (n + n)) → ℝ) :
    twoSpaceSwap n z 0 = z 0 := by
  change (timeTwoSpaceCoordinates n (twoSpaceSwap n z)).1 = (timeTwoSpaceCoordinates n z).1
  rw [timeTwoSpaceCoordinates_twoSpaceSwap]

/-- Spatial exchange preserves full coordinate Lebesgue measure. -/
theorem measurePreserving_twoSpaceSwap (n : ℕ) : MeasurePreserving (twoSpaceSwap n) := by
  have hs : MeasurePreserving (Prod.swap : ((Fin n → ℝ) × (Fin n → ℝ)) → _)
      volume volume := by
    simpa only [← Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure (Fin n → ℝ)))
        (ν := (volume : Measure (Fin n → ℝ))))
  have hp : MeasurePreserving (fun p : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => (p.1, p.2.swap))
      volume volume := by
    simpa only [← Measure.volume_eq_prod, Prod.map_def, id_eq] using (MeasurePreserving.id (volume : Measure ℝ)).prod hs
  have he := measurePreserving_timeTwoSpaceCoordinates n
  have hi := MeasurePreserving.symm (timeTwoSpaceCoordinates n).toHomeomorph.toMeasurableEquiv he
  exact hi.comp (hp.comp he)

/-- Spatial exchange preserves coordinate measure restricted to positive time. -/
theorem measurePreserving_twoSpaceSwap_positive (n : ℕ) :
    MeasurePreserving (twoSpaceSwap n)
      (volume.restrict {z : Fin (1 + (n + n)) → ℝ | 0 < z 0})
      (volume.restrict {z : Fin (1 + (n + n)) → ℝ | 0 < z 0}) := by
  have h := (measurePreserving_twoSpaceSwap n).restrict_preimage_emb
    (twoSpaceSwap n).toHomeomorph.measurableEmbedding {z | 0 < z 0}
  simpa only [Set.preimage_ofPred_eq, twoSpaceSwap_time] using h

end HeatKernel

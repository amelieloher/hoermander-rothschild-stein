-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CoordinateMeasure
public import HeatKernel.Kernel.EveryTimeRepresentatives

/-! # Every-time representatives in spacetime coordinates

The coordinate equivalence preserves the measures restricted to positive time.
It therefore transports almost-everywhere representatives to the product measure
used for identifying every L² time section.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- The time-space split preserves Lebesgue measure restricted to positive time. -/
theorem measurePreserving_timeSpaceCoordinates_positive (n : ℕ) :
    MeasurePreserving (timeSpaceCoordinates n)
      (volume.restrict {x : Fin (1 + n) → ℝ | 0 < x 0})
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
  have hpre : timeSpaceCoordinates n ⁻¹' (Set.Ioi (0 : ℝ) ×ˢ Set.univ) =
      {x | 0 < x 0} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true,
      timeSpaceCoordinates_fst, Set.mem_ofPred_eq]
  rw [Measure.restrict_prod_eq_prod_univ, ← Measure.volume_eq_prod]
  have h := (measurePreserving_timeSpaceCoordinates n).restrict_preimage_emb
    (timeSpaceCoordinates n).toHomeomorph.measurableEmbedding
    (Set.Ioi (0 : ℝ) ×ˢ Set.univ)
  rw [hpre] at h
  exact h

end HeatKernel

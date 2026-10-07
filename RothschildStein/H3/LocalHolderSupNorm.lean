-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderSubsetContinuity
public import RothschildStein.S.HolderBounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal
namespace RothschildStein.H3

/-- A local full fixed Hölder norm controls the actual
essential supremum on the same open set. Measurability is derived
from the shared ambient distance geometry and positive exponent. -/
theorem eLpNorm_top_le_local_holderNorm {N : ℕ}
    (Ω U : Opens (Fin N → ℝ)) (G : S.DistanceGeometry Ω)
    (hU : (U : Set (Fin N → ℝ)) ⊆ Ω) {α : ℝ} (hα : 0 < α)
    {f : (Fin N → ℝ) → ℝ}
    (hf : holderENorm G.d α (U : Set (Fin N → ℝ)) f < ⊤) :
    eLpNorm f ⊤ (volume.restrict (U : Set (Fin N → ℝ))) ≤
      holderENorm G.d α (U : Set (Fin N → ℝ)) f := by
  have hm : AEStronglyMeasurable f (volume.restrict (U : Set (Fin N → ℝ))) := (S.continuousOn_of_holderENorm_lt_top_subset Ω G hU hα hf).aestronglyMeasurable U.isOpen.measurableSet
  rw [eLpNorm_exponent_top hm]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  rw [ae_restrict_iff' U.isOpen.measurableSet]
  filter_upwards [] with x
  intro hx
  simpa only [Real.enorm_eq_ofReal_abs] using
    S.enorm_le_holderENorm G.d α (U : Set (Fin N → ℝ)) f hx

/-- The normalized local Hölder representatives are actual
L infinity inputs, with no auxiliary measurable representative premise. -/
theorem memLp_top_of_local_holderNorm {N : ℕ}
    (Ω U : Opens (Fin N → ℝ)) (G : S.DistanceGeometry Ω)
    (hU : (U : Set (Fin N → ℝ)) ⊆ Ω) {α : ℝ} (hα : 0 < α)
    {f : (Fin N → ℝ) → ℝ}
    (hf : holderENorm G.d α (U : Set (Fin N → ℝ)) f < ⊤) :
    MemLp f ⊤ (volume.restrict (U : Set (Fin N → ℝ))) := by
  exact (eLpNorm_top_le_local_holderNorm Ω U G hU hα hf).trans_lt hf

end RothschildStein.H3

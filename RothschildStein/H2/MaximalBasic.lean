-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.LocalAverage
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Metric MeasureTheory
open scoped ENNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
/-- Every strict superlevel is a union of the eligible open balls
(BB Definition 7.24 and Theorem 7.25, pp. 313–314). -/
theorem patchMaximal_superlevel (μ : Measure X) (S : Set X) (ρ : ℝ)
    (f : X → ℝ) (t : ℝ≥0∞) :
    {x | t < patchMaximal μ S ρ f x} =
      ⋃ i ∈ {i : X × ℝ | i.1 ∈ S ∧ i.2 ∈ Ioc 0 ρ ∧
        t < ⨍⁻ y in ball i.1 i.2, ‖f y‖ₑ ∂μ}, ball i.1 i.2 := by
  ext x
  simp only [mem_ofPred_eq, patchMaximal, lt_iSup_iff, mem_iUnion, mem_ball]
  constructor
  · rintro ⟨z, hz, r, hr, hdist, havg⟩
    exact ⟨(z,r), ⟨hz,hr,havg⟩, hdist⟩
  · rintro ⟨⟨z,r⟩, ⟨hz,hr,havg⟩, hdist⟩
    exact ⟨z,hz,r,hr,hdist,havg⟩

omit [BorelSpace X] in
/-- The local maximal function is lower semicontinuous, even
without measurability of the input (BB pp. 313–314). -/
theorem lowerSemicontinuous_patchMaximal (μ : Measure X) (S : Set X) (ρ : ℝ)
    (f : X → ℝ) : LowerSemicontinuous (patchMaximal μ S ρ f) := by
  apply lowerSemicontinuous_iff_isOpen_preimage.mpr
  intro t
  change IsOpen {x | t < patchMaximal μ S ρ f x}
  rw [patchMaximal_superlevel]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball

end RothschildStein.H2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.Patches
public import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Compact centre closure and positive small balls give a positive uniform
lower bound. BB Lemma 7.47, p. 333; a finite cover also handles boundary centres. -/
theorem DoublingPatch.exists_uniform_lower (P : DoublingPatch X) {s : ℝ}
    (hs : 0 < s) (hκ : s ≤ 6 * P.ρ) :
    ∃ m : ℝ≥0∞, 0 < m ∧ ∀ z ∈ P.S, m ≤ P.μ (ball z s) := by
  classical
  have hc : closure P.S ⊆ ⋃ z : P.S, ball (z : X) (s / 2) := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.mp hx (s / 2) (by linarith)
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, by simpa [mem_ball] using hxz⟩
  obtain ⟨J, hJ⟩ := P.compact_closure.elim_finite_subcover
    (fun z : P.S => ball (z : X) (s / 2)) (fun _ => isOpen_ball) hc
  refine ⟨J.inf (fun z => P.μ (ball (z : X) (s / 2))), ?_, ?_⟩
  · apply (Finset.lt_inf_iff (by simp : (0 : ℝ≥0∞) < ⊤)).mpr
    intro z _
    exact (P.doubling z z.property (s / 2) (by linarith) (by linarith)).1
  · intro x hx
    obtain ⟨z, hzJ, hz⟩ := mem_iUnion₂.mp (hJ (subset_closure hx))
    refine (Finset.inf_le hzJ).trans (measure_mono ?_)
    intro y hy
    rw [mem_ball] at hz hy ⊢
    have hxy := dist_triangle y (z : X) x
    rw [dist_comm (z : X) x] at hxy
    linarith

/-- The literal infimum formulation; the empty centre set has value ∞. -/
theorem DoublingPatch.iInf_volume_pos (P : DoublingPatch X) {s : ℝ}
    (hs : 0 < s) (hκ : s ≤ 6 * P.ρ) :
    0 < ⨅ z : P.S, P.μ (ball (z : X) s) := by
  obtain ⟨m, hm, hb⟩ := P.exists_uniform_lower hs hκ
  exact hm.trans_le (le_iInf fun z => hb z z.property)

end RothschildStein.H2

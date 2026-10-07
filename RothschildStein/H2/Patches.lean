-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.LocDoubling
public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The doubling inequality in patch-radius form, from BB (7.2), p. 295. -/
theorem LocDoubling.doubling_half (D : LocDoubling X) {z : X} (hz : z ∈ D.Ω₁)
    {s : ℝ} (hs : 0 < s) (hsκ : s ≤ 6 * D.κ) :
    0 < D.μ (ball z s) ∧ D.μ (ball z s) < ⊤ ∧
      D.μ (ball z s) ≤ ENNReal.ofReal D.C_D * D.μ (ball z (s / 2)) := by
  obtain ⟨hp, hd, _⟩ := D.doubling z hz (s / 2) (by linarith) (by linarith)
  have he : 2 * (s / 2) = s := by ring
  rw [he] at hp hd
  have hf : D.μ (ball z s) < ⊤ :=
    lt_of_le_of_lt (measure_mono ((ball_subset_ball hsκ).trans
      (ball_subset_closedBall.trans (D.incl₁ z hz)))) D.finΩ₂
  exact ⟨hp, hf, hd⟩

/-- The outer patch (Ω₁, Ω₂, κ, C_D). -/
def LocDoubling.outerPatch (D : LocDoubling X) : DoublingPatch X where
  μ := D.μ
  S := D.Ω₁
  W := D.Ω₂
  ρ := D.κ
  C_D := D.C_D
  ρ_pos := D.κ_pos
  one_lt_C_D := D.one_lt_C_D
  incl := fun z hz => ball_subset_closedBall.trans (D.incl₁ z hz)
  doubling := fun _z hz _ hs hκ => D.doubling_half hz hs hκ
  measurable_W := D.open₂.measurableSet
  finite_W := D.finΩ₂
  compact_closure := D.cpt.of_isClosed_subset isClosed_closure (closure_mono D.sub₁₂)
  noAtoms := D.noAtoms

end RothschildStein.H2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HomogeneousBounds
public import RothschildStein.H1.WordBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Every gauge derivative word has degree one minus its weighted length.
Weighted homogeneity and compactness of the unit sphere give its global
bound without a derivative-size hypothesis. -/
theorem gauge_wordDerivative_bound (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) (I : List (Fin (q + 1))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, x ≠ 0 →
      |wordDerivative H.fields I ν x| ≤
        M * (ν x) ^ (1 - (H1.differentialWordWeight I : ℝ)) := by
  have hh : ∀ t : ℝ, 0 < t → ∀ x : Fin N → ℝ, x ≠ 0 →
      ν (G.dilate t x) = t ^ (1 : ℝ) * ν x := by
    intro t ht x _
    rw [Real.rpow_one]
    exact ν.gauge.2.2.2 t ht x
  obtain ⟨M, hM, _, _, hb⟩ := homogeneous_function_sphere_bound ν.gauge
    (1 - (H1.differentialWordWeight I : ℝ))
    (H.wordDerivative_smooth_off_zero G hν I).continuousOn
    (H.wordDerivative_homogeneous G hν hh I)
  exact ⟨M, hM, hb⟩

/-- Horizontal first derivatives of the gauge have uniform degree
zero bounds at every nonzero point. -/
theorem gauge_horizontalDerivative_bound (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) (i : Fin q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, x ≠ 0 → |fieldDerivative (H.fields i.succ) ν x| ≤ M := by
  obtain ⟨M, hM, hb⟩ := gauge_wordDerivative_bound G H ν hν [i.succ]
  refine ⟨M, hM, ?_⟩
  intro x hx
  simpa [wordDerivative, H1.differentialWordWeight, Fin.succ_ne_zero] using hb x hx

end RothschildStein.H3

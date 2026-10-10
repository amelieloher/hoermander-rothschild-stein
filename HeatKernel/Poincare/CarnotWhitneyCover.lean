-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.BallBoundary
public import HeatKernel.Poincare.CarnotSphere

/-! Countable interior Whitney covers for homogeneous horizontal balls. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open TopologicalSpace Set Metric RothschildStein

namespace HeatKernel.CarnotPoint

/-- Every positive-radius horizontal metric ball has a countable disjoint Whitney family,
covered by fivefold dilates whose eightyfold dilates remain in the original ball. -/
theorem exists_countable_disjoint_boundaryBall_cover {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r κ : ℝ} (hr : 0 < r) (hκ : 80 < κ) :
    ∃ C : Set (CarnotPoint G hq hqpos hspan), C ⊆ ball x r ∧ C.Countable ∧
      (C.PairwiseDisjoint fun z => ball z (infDist z (ball x r)ᶜ / κ)) ∧
      ball x r = ⋃ z ∈ C, ball z (5 * (infDist z (ball x r)ᶜ / κ)) ∧
      ∀ z ∈ C, ball z (80 * (infDist z (ball x r)ᶜ / κ)) ⊆ ball x r := by
  let : SeparableSpace (CarnotPoint G hq hqpos hspan) :=
    inferInstanceAs (SeparableSpace (Fin N → ℝ))
  obtain ⟨w, hw'⟩ := exists_dist_eq G hq hqpos hspan hw x hr
  exact HeatKernel.exists_countable_disjoint_boundaryBall_cover_of_sphere_point x w hw' hκ

end HeatKernel.CarnotPoint

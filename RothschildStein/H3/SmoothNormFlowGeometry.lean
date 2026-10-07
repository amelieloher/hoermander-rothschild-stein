-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SmoothNormGeometry
public import RothschildStein.H3.GlobalSobolevDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- The full estimate follows from exact geometry and horizontal flows,
with global smooth Sobolev density now proved internally. -/
theorem smoothNorm_estimate_of_geometry_flow {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    (P : G2.ControlNormConclusion G driftWeight H.fields)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hp₁ : 1 < p.toReal)
    (E : Fin q → ℝ → (Fin n → ℝ))
    (hE : ∀ i, Continuous (E i)) (hE0 : ∀ i, E i 0 = 0)
    (hflow : ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => H.fields i.succ))
 :
    ∃ A : ℝ, 0 < A ∧ HalfRadiusEstimate G (G2.smoothNorm G) H.fields p A := by
  let hpFact : Fact (1 ≤ p) := ⟨hp⟩
  have hdensity : ∀ v, memSobolevX driftWeight H.fields ⊤ 2 p v →
      Nonempty (SobolevWordApproximation driftWeight H.fields p v) :=
    fun v hv => exists_sobolevWordApproximation_global_ennreal G H hpt hp₁.le hv
  exact smoothNorm_estimate_of_geometry_flow_and_density G H K hQ P p hp hpt hp₁ E hE hE0 hflow hdensity

end RothschildStein.H3

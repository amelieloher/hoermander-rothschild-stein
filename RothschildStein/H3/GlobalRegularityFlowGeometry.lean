-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GlobalRegularityGeometry
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
theorem exists_global_regularity_constant_of_geometry_flow {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (P : G2.ControlNormConclusion G driftWeight H.fields)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (p r : ℝ≥0∞) [hpFact : Fact (1 ≤ p)] [hrFact : Fact (1 ≤ r)]
    [hpr : ENNReal.HolderConjugate p r] (hpt : p ≠ ∞)
    (hp₁ : 1 < p.toReal)
    (E : Fin q → ℝ → (Fin n → ℝ))
    (hE : ∀ i, Continuous (E i)) (hE0 : ∀ i, E i 0 = 0)
    (hflow : ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => H.fields i.succ))
 :
    ∃ C : ℝ, 0 < C ∧ ∀ u g : (Fin n → ℝ) → ℝ,
      MemLp u p (volume : Measure (Fin n → ℝ)) → MemLp g p volume →
      hasDistributionEquationWithDrift ⊤ H.fields (fun i => (H.fields_smooth G i).contDiffOn)
        (Distribution.ofFun ⊤ u volume (⊤ : ℕ∞)) g →
      memSobolevX driftWeight H.fields ⊤ 2 p u ∧
        driftSecondWeakENorm H.fields ⊤ p u ≤ ENNReal.ofReal C * eLpNorm g p volume ∧
        sobolevXENorm driftWeight H.fields ⊤ 2 p u ≤
          ENNReal.ofReal C * (eLpNorm u p volume + eLpNorm g p volume) ∧
        (∑ I ∈ (wordFamily driftWeight 2).filter (fun I => wordWeight driftWeight I = 1),
          weakWordENorm H.fields ⊤ I p u) ≤
          ENNReal.ofReal C * (eLpNorm u p volume + eLpNorm g p volume) := by
  have hdensity : ∀ v, memSobolevX driftWeight H.fields ⊤ 2 p v →
      Nonempty (SobolevWordApproximation driftWeight H.fields p v) :=
    fun v hv => exists_sobolevWordApproximation_global_ennreal G H hpt hp₁.le hv
  exact exists_global_regularity_constant_of_geometry_flow_and_density G H K hQ P ν h1 hsym p r hpt hp₁ E hE hE0 hflow hdensity

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GlobalRegularityConditional

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal

/-- A positive global regularity constant, uniform in u and g, under the
flow, density, and half-radius estimate hypotheses. Local regularity and
the PDE representative are also assumed. -/
theorem exists_global_regularity_constant_of_flow_density_and_halfRadius {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (E : Fin q → ℝ → (Fin n → ℝ)) (hE : ∀ i, Continuous (E i))
    (hE0 : ∀ i, E i 0 = 0)
    (hflow : ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => H.fields i.succ))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hdensity : ∀ u, memSobolevX driftWeight H.fields ⊤ 2 p u →
      Nonempty (SobolevWordApproximation driftWeight H.fields p u))
    (K : ℝ) (hK : 0 ≤ K) (hest : HalfRadiusEstimate G ν H.fields p K) :
    ∃ C : ℝ, 0 < C ∧ ∀ u g : (Fin n → ℝ) → ℝ,
      MemLp u p (volume : Measure (Fin n → ℝ)) → MemLp g p volume →
      (∀ R : ℝ, 0 < R →
        memSobolevX driftWeight H.fields (quasiballDomain G ν 0 R) 2 p u ∧
        ∃ D : WeakDriftOperatorData H.fields (quasiballDomain G ν 0 R) p u,
          D.operator =ᵐ[volume.restrict (G2.gaugeBall G ν 0 R)] g) →
      memSobolevX driftWeight H.fields ⊤ 2 p u ∧
        sobolevXENorm driftWeight H.fields ⊤ 2 p u ≤
          ENNReal.ofReal C * (eLpNorm u p volume + eLpNorm g p volume) := by
  obtain ⟨cE, δE, hcE, hδE, hinterp⟩ := zeroCenteredPhiInterpolation_of_flow_and_density
    G H ν hν E hE hE0 hflow p hp hpt hdensity
  have hC : 0 < globalRegularityConstant q K cE := by
    unfold globalRegularityConstant
    positivity
  refine ⟨globalRegularityConstant q K cE, hC, ?_⟩
  intro u g hu hg hlocal
  exact global_regularity_of_halfRadius_and_interpolation G ν H.fields hp hpt
    K cE δE hK hcE.le hδE hest hu hg hlocal (hinterp u)

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.InterpolationFullSecond

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal

/-- Phi interpolation at the origin with the full weighted second Phi;
local Sobolev membership is the source hypothesis. -/
def ZeroCenteredPhiInterpolation {n q : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ) (cE δE : ℝ) : Prop :=
  ∀ R : ℝ, 0 < R → memSobolevX driftWeight X (quasiballDomain G ν 0 R) 2 p u →
    let N₀ := fun σ => (eLpNorm u p (volume.restrict (G2.gaugeBall G ν 0 (σ * R)))).toReal
    let N₁ := fun σ => (horizontalWeakENorm X (quasiballDomain G ν 0 (σ * R)) p u).toReal
    let N₂ := fun σ => (driftSecondWeakENorm X (quasiballDomain G ν 0 (σ * R)) p u).toReal
    ∀ δ : ℝ, 0 < δ → δ ≤ δE →
      phi (Ioo (1 / 2 : ℝ) 1) R 1 N₁ ≤
        ENNReal.ofReal δ * phi (Ioo (1 / 2 : ℝ) 1) R 2 N₂ +
        ENNReal.ofReal (cE / δ) * phi (Ioo (1 / 2 : ℝ) 1) R 0 N₀

/-- The flow and density hypotheses give the interpolation estimate with
constants uniform in the input and radius. -/
theorem zeroCenteredPhiInterpolation_of_flow_and_density {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (E : Fin q → ℝ → (Fin n → ℝ)) (hE : ∀ i, Continuous (E i))
    (hE0 : ∀ i, E i 0 = 0)
    (hflow : ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => H.fields i.succ))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hdensity : ∀ u, memSobolevX driftWeight H.fields ⊤ 2 p u →
      Nonempty (SobolevWordApproximation driftWeight H.fields p u)) :
    ∃ cE δE : ℝ, 0 < cE ∧ 0 < δE ∧
      ∀ u : (Fin n → ℝ) → ℝ, ZeroCenteredPhiInterpolation G ν H.fields p u cE δE := by
  obtain ⟨cE, δE, hcE, hδE, hb⟩ := interpolation_full_second_of_flow_and_density G H ν hν
  refine ⟨cE, δE, hcE, hδE, ?_⟩
  intro u R hR hu
  exact hb E hE hE0 hflow p hp hpt hdensity 0 R hR u hu

end RothschildStein.H3

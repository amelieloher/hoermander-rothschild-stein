-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.InterpolationUniform
public import RothschildStein.H3.DriftSecondPhiFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal

/-- The uniform interpolation estimate controls the first
Phi using the complete weighted second Phi, including mixed words and drift. -/
theorem interpolation_full_second_of_flow_and_density {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) :
    ∃ cE δE : ℝ, 0 < cE ∧ 0 < δE ∧
      ∀ (E : Fin q → ℝ → (Fin n → ℝ))
    (_hE : ∀ i, Continuous (E i)) (_hE0 : ∀ i, E i 0 = 0)
    (_hflow : ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => H.fields i.succ))
    (p : ℝ≥0∞) (_hp : 1 ≤ p) (_hpt : p ≠ ∞)
    (_hdensity : ∀ u, memSobolevX driftWeight H.fields ⊤ 2 p u →
      Nonempty (SobolevWordApproximation driftWeight H.fields p u)),
      ∀ x₀ : Fin n → ℝ, ∀ r : ℝ, 0 < r →
      ∀ u : (Fin n → ℝ) → ℝ,
        memSobolevX driftWeight H.fields (quasiballDomain G ν x₀ r) 2 p u →
      let N₀ := fun σ => (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ (σ*r)))).toReal
      let N₁ := fun σ => (horizontalWeakENorm H.fields (quasiballDomain G ν x₀ (σ*r)) p u).toReal
      let N₂ := fun σ => (driftSecondWeakENorm H.fields (quasiballDomain G ν x₀ (σ*r)) p u).toReal
      ∀ δ : ℝ, 0 < δ → δ ≤ δE →
        phi (Ioo (1/2 : ℝ) 1) r 1 N₁ ≤
          ENNReal.ofReal δ*phi (Ioo (1/2 : ℝ) 1) r 2 N₂ +
          ENNReal.ofReal (cE/δ)*phi (Ioo (1/2 : ℝ) 1) r 0 N₀ := by
  obtain ⟨cE,δE,hcE,hδE,hb⟩ := interpolation_uniform_of_flow_and_density G H ν hν
  refine ⟨cE,δE,hcE,hδE,?_⟩
  intro E hE hE0 hflow p hp hpt hdensity x₀ r hr u hu
  dsimp only
  intro δ hδ hd
  have hfirst := hb E hE hE0 hflow p hp hpt hdensity x₀ r hr u hu δ hδ hd
  have hsecond := phi_horizontalSquare_le_driftSecond G ν H.fields x₀ hr p u hu
  exact hfirst.trans (add_le_add (mul_le_mul' (le_refl _) hsecond) le_rfl)

end RothschildStein.H3

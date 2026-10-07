-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballRealConstants
public import RothschildStein.H3.QuasiballTestCutoff
public import RothschildStein.H3.WeakHorizontalRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal

/-- The geometry constants are uniform in the exponent, center, radius,
and Sobolev input under the global flow and density hypotheses
(BB Theorem 8.42, p. 371). -/
theorem interpolation_uniform_of_flow_and_density {n q : ℕ}
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
      let N₂ := fun σ => (horizontalSquareWeakENorm H.fields (quasiballDomain G ν x₀ (σ*r)) p u).toReal
      ∀ δ : ℝ, 0 < δ → δ ≤ δE →
        phi (Ioo (1/2 : ℝ) 1) r 1 N₁ ≤
          ENNReal.ofReal δ*phi (Ioo (1/2 : ℝ) 1) r 2 N₂ +
          ENNReal.ofReal (cE/δ)*phi (Ioo (1/2 : ℝ) 1) r 0 N₀ := by
  obtain ⟨c₁,c₂,hc₁,hc₂,hcut⟩ := exists_quasiball_test_cutoff G H ν hν
  let c := cutoffInterpolationConstant (q : ℝ) c₁ c₂
  have hq : 0 < (q : ℝ) := by exact_mod_cast H.q_pos
  have hc : 0 < c := lt_of_lt_of_le (by positivity : 0 < 4*c₁) (le_max_left _ _)
  refine ⟨32*c,min 8 (2/c),by positivity,by positivity,?_⟩
  intro E hE hE0 hflow p hp hpt hdensity x₀ r hr u hu
  have hstep := quasiball_real_step_with_constants G H ν c₁ c₂ hcut hc₁ hc₂
    E hE hE0 hflow hp hpt hdensity
  let N₀ := fun σ => (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ (σ*r)))).toReal
  let N₁ := fun σ => (horizontalWeakENorm H.fields (quasiballDomain G ν x₀ (σ*r)) p u).toReal
  let N₂ := fun σ => (horizontalSquareWeakENorm H.fields (quasiballDomain G ν x₀ (σ*r)) p u).toReal
  obtain ⟨CE,DE,hCE,hDE,he,hd,hb⟩ := phi_interpolation_of_cutoff_step
    (Ioo (1/2 : ℝ) 1) N₀ N₁ N₂ hr hq (Or.inl rfl)
    (phi_horizontalWeak_lt_top G ν H.fields x₀ hr p u hu).ne
    (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => ENNReal.toReal_nonneg)
    (hstep x₀ r hr u hu)
  rw [he,hd] at hb
  exact hb

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalCutoffInterpolation
public import RothschildStein.H3.QuasiballDomain
public import RothschildStein.Definitions.driftWeight
public import RothschildStein.H1.Standing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- Interpolation uses a fixed family of cutoff constants for every exponent. -/
theorem quasiball_interpolation_step_with_constants {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G)
    (c₁ c₂ : ℝ)
    (hcut : ∀ x₀ : Fin n → ℝ, ∀ t s : ℝ, 0 < t → t < s → s/2 ≤ t →
      ∃ φ : TestFunction (quasiballDomain G ν x₀ s) ℝ (⊤ : ℕ∞),
        EqOn φ 1 (G2.gaugeBall G ν x₀ t) ∧ eLpNorm φ ⊤ volume ≤ 1 ∧
        (∀ i : Fin q, eLpNorm (fieldDerivative (H.fields i.succ) φ) ⊤ volume ≤
          ENNReal.ofReal (c₁/(s-t))) ∧
        (∀ i j : Fin q, eLpNorm (fieldDerivative (H.fields i.succ)
          (fieldDerivative (H.fields j.succ) φ)) ⊤ volume ≤
          ENNReal.ofReal (c₂/(s-t)^2)))
    (E : Fin q → ℝ → (Fin n → ℝ))
    (hE : ∀ i, Continuous (E i)) (hE0 : ∀ i, E i 0 = 0)
    (hflow : ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => H.fields i.succ))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hdensity : ∀ u, memSobolevX driftWeight H.fields ⊤ 2 p u →
      Nonempty (SobolevWordApproximation driftWeight H.fields p u)) :
      ∀ x₀ : Fin n → ℝ, ∀ t s : ℝ, 0 < t → t < s → s/2 ≤ t →
      ∀ u : (Fin n → ℝ) → ℝ,
        memSobolevX driftWeight H.fields (quasiballDomain G ν x₀ s) 2 p u →
      ∀ ε : ℝ, 0 < ε →
      (∑ i : Fin q, weakWordENorm H.fields (quasiballDomain G ν x₀ t) [i.succ] p u) ≤
        ENNReal.ofReal (2*(q : ℝ)/ε)*
          eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ s)) +
        ENNReal.ofReal (ε/2)*
          ((∑ i : Fin q, weakWordENorm H.fields (quasiballDomain G ν x₀ s) [i.succ,i.succ] p u) +
            2*ENNReal.ofReal (c₁/(s-t))*
              (∑ i : Fin q, weakWordENorm H.fields (quasiballDomain G ν x₀ s) [i.succ] p u) +
            (q : ℝ≥0∞)*ENNReal.ofReal (c₂/(s-t)^2)*
              eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ s))) := by
  intro x₀ t s ht hts hhalf u hu ε hε
  obtain ⟨φ,hone,hφ,hfirst,hsecond⟩ := hcut x₀ t s ht hts hhalf
  have htop : eLpNorm φ ⊤ (volume.restrict (G2.gaugeBall G ν x₀ s)) ≤ 1 :=
    (eLpNorm_mono_measure φ (Measure.restrict_le_self)).trans hφ
  have hA : ∀ i : Fin q, eLpNorm (fieldDerivative (H.fields i.succ) φ) ⊤
      (volume.restrict (G2.gaugeBall G ν x₀ s)) ≤ ENNReal.ofReal (c₁/(s-t)) := by
    intro i
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hfirst i)
  have hB : ∀ i : Fin q, eLpNorm
      (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields i.succ) φ)) ⊤
      (volume.restrict (G2.gaugeBall G ν x₀ s)) ≤ ENNReal.ofReal (c₂/(s-t)^2) := by
    intro i
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hsecond i i)
  have hweight : ∀ i : Fin q, (driftWeight i.succ : ℕ) = 1 := by
    intro i
    simp [driftWeight, Fin.succ_ne_zero]
  exact local_cutoff_interpolation_of_flow_and_density G driftWeight H.fields
    (H.fields_smooth G) Fin.succ hweight E hE hE0 hflow hp hpt hdensity
    (quasiballDomain G ν x₀ s) (quasiballDomain G ν x₀ t) hu φ hone
    (ENNReal.ofReal (c₁/(s-t))) (ENNReal.ofReal (c₂/(s-t)^2)) htop hA hB hε

end RothschildStein.H3

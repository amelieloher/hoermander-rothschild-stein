-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballDriftTestCutoff
public import RothschildStein.H3.CompactDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- The quasiball second-word estimate uses the smooth cutoff bounds,
the compact second-order estimate, and global density. Its cutoff constants
are uniform over exponents, centers, radii, and inputs. -/
theorem quasiball_step_of_compact_and_density {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (p : ℝ≥0∞) (_hp : 1 ≤ p) (C : ℝ)
      (_hcompact : ∀ v : (Fin n → ℝ) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) v → HasCompactSupport v →
        ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
          eLpNorm (wordDerivative H.fields I v) p volume ≤
            ENNReal.ofReal C * eLpNorm (sumSquaresWithDrift H.fields v) p volume)
      (_hdensity : ∀ v, memSobolevX driftWeight H.fields ⊤ 2 p v →
        Nonempty (SobolevWordApproximation driftWeight H.fields p v)),
      ∀ x₀ : Fin n → ℝ, ∀ t s : ℝ, 0 < t → t < s → s/2 ≤ t →
      ∀ u : (Fin n → ℝ) → ℝ,
        memSobolevX driftWeight H.fields (quasiballDomain G ν x₀ s) 2 p u →
      ∀ D : WeakDriftOperatorData H.fields (quasiballDomain G ν x₀ s) p u,
      ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
        weakWordENorm H.fields (quasiballDomain G ν x₀ t) I p u ≤
          ENNReal.ofReal C *
            (eLpNorm D.operator p (volume.restrict (G2.gaugeBall G ν x₀ s)) +
              (q+1 : ℝ≥0∞) * ENNReal.ofReal (c₂/(s-t)^2) *
                eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ s)) +
              2 * ENNReal.ofReal (c₁/(s-t)) *
                ∑ i : Fin q, weakWordENorm H.fields (quasiballDomain G ν x₀ s) [i.succ] p u) := by
  obtain ⟨c₁,c₂,hc₁,hc₂,hcut⟩ := exists_quasiball_drift_test_cutoff G H ν hν
  refine ⟨c₁,c₂,hc₁,hc₂,?_⟩
  intro p hp C hcompact hdensity x₀ t s ht hts hhalf u hu D I hI
  obtain ⟨φ,hone,hφ,hfirst,hL⟩ := hcut x₀ t s ht hts hhalf
  have htop : eLpNorm φ ⊤ (volume.restrict (G2.gaugeBall G ν x₀ s)) ≤ 1 :=
    (eLpNorm_mono_measure φ Measure.restrict_le_self).trans hφ
  have hA : ∀ i : Fin q, eLpNorm (fieldDerivative (H.fields i.succ) φ) ⊤
      (volume.restrict (G2.gaugeBall G ν x₀ s)) ≤ ENNReal.ofReal (c₁/(s-t)) :=
    fun i => (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hfirst i)
  have hB : eLpNorm (sumSquaresWithDrift H.fields φ) ⊤
      (volume.restrict (G2.gaugeBall G ν x₀ s)) ≤
      (q+1 : ℝ≥0∞) * ENNReal.ofReal (c₂/(s-t)^2) :=
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hL
  exact local_second_word_of_compact_and_density H.fields (H.fields_smooth G)
    p hp C hcompact hdensity (quasiballDomain G ν x₀ s) (quasiballDomain G ν x₀ t)
    u hu D φ hone (ENNReal.ofReal (c₁/(s-t)))
    ((q+1 : ℝ≥0∞) * ENNReal.ofReal (c₂/(s-t)^2)) htop hA hB I hI

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffWordLp

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The first- and second-order cutoff bounds used in interpolation and
half-radius estimates. Their constants are uniform over the finite
derivative families, centers, and radii. Higher word estimates are separate. -/
theorem exists_quasiball_cutoff_lowOrder (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ x₀ : Fin N → ℝ, ∀ t s : ℝ, 0 < t → t < s → s/2 ≤ t →
        ∃ φ : (Fin N → ℝ) → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
          (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
          EqOn φ (fun _ => 1) (G2.gaugeBall G ν x₀ t) ∧
          tsupport φ ⊆ G2.gaugeClosedBall G ν x₀ ((t+s)/2) ∧
          G2.gaugeClosedBall G ν x₀ ((t+s)/2) ⊆ G2.gaugeBall G ν x₀ s ∧
          (∀ i : Fin q, eLpNorm (fieldDerivative (H.fields i.succ) φ) ⊤ volume ≤
            ENNReal.ofReal (c₁ / (s-t))) ∧
          (eLpNorm (fieldDerivative (H.fields 0) φ) ⊤ volume ≤
            ENNReal.ofReal (c₂ / (s-t)^2)) ∧
          (∀ i j : Fin q, eLpNorm (fieldDerivative (H.fields i.succ)
            (fieldDerivative (H.fields j.succ) φ)) ⊤ volume ≤ ENNReal.ofReal (c₂ / (s-t)^2)) := by
  obtain ⟨c₁,c₂,hc₁,hc₂,hb⟩ := exists_cutoff_first_second_Linfinity G H ν hν
  refine ⟨c₁,c₂,hc₁,hc₂,?_⟩
  intro x₀ t s ht hts hhalf
  obtain ⟨hfirst,hdrift,hsecond⟩ := hb x₀ t s ht hts hhalf
  exact ⟨smoothQuasiballCutoff G ν x₀ t s,
    smoothQuasiballCutoff_contDiff G ν hν x₀ ht hts,
    smoothQuasiballCutoff_compact G ν x₀ hts,
    fun x => smoothQuasiballCutoff_range G ν x₀ x t s,
    smoothQuasiballCutoff_one G ν x₀ hts,
    smoothQuasiballCutoff_tsupport G ν x₀ hts,
    intermediate_quasiball_subset G ν x₀ hts,hfirst,hdrift,hsecond⟩

end RothschildStein.H3

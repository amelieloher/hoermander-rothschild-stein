-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballCutoffHolder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- An upper gap bound combines the supremum and seminorm
into one inverse power. The upper scale is retained in the constant. -/
theorem cutoff_holder_full_power_bound {a S c α : ℝ} (ha : 0 < a)
    (haS : a ≤ S) (hc : 0 ≤ c) (hα : 0 ≤ α) (k : ℕ) :
    c / a ^ k * (1 + 2 / a ^ α) ≤
      (c * (S ^ α + 2)) / a ^ ((k : ℝ) + α) := by
  have hp : 0 < a ^ α := Real.rpow_pos_of_pos ha α
  have hk : 0 < a ^ k := pow_pos ha k
  have he : a ^ ((k : ℝ) + α) = a ^ k * a ^ α := by
    rw [Real.rpow_add ha, Real.rpow_natCast]
  rw [he]
  calc
    _ = (c * (a ^ α + 2)) / (a ^ k * a ^ α) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add (Real.rpow_le_rpow ha.le haS hα) le_rfl) hc)
      (mul_nonneg hk.le hp.le)

/-- Exact full Hölder powers for every fixed ordered word
of the actual cutoff. There is one constant per word and fixed upper
scale, uniformly in the center and both radii (BB p. 384). -/
theorem exists_quasiball_cutoff_word_holder_power_constants {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {α : ℝ≥0} (hα1 : (α : ℝ) ≤ 1) {S₀ : ℝ} (hS₀ : 0 < S₀) :
    ∃ C : List (Fin (q + 1)) → ℝ, (∀ I, 0 < C I) ∧
      ∀ I (x₀ : Fin N → ℝ) (t s : ℝ), 0 < t → t < s → s / 2 ≤ t → s - t ≤ S₀ →
      let metric := gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
      @H2.boundedHolderNorm (ControlCarrier N) metric α univ
        (wordDerivative H.fields I (smoothQuasiballCutoff G ν x₀ t s)) ≤
      ENNReal.ofReal (C I / (s - t) ^ ((H1.differentialWordWeight I : ℝ) + (α : ℝ))) := by
  obtain ⟨B, hB, hb⟩ := exists_quasiball_cutoff_word_holder_constants G H Hc ν hν hα1
  refine ⟨fun I => B I * (S₀ ^ (α : ℝ) + 2), fun I => mul_pos (hB I) (by positivity), ?_⟩
  intro I x₀ t s ht hts hhalf hgap
  exact (hb I x₀ t s ht hts hhalf).trans (ENNReal.ofReal_le_ofReal
    (cutoff_holder_full_power_bound (sub_pos.mpr hts) hgap (hB I).le α.coe_nonneg _))

end RothschildStein.H3

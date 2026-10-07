-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballCutoffSemi

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- The smooth-gauge cutoff has Lipschitz constant L/epsilon at every
positive scale and vanishes outside its epsilon ball. The constants are
uniform in epsilon under the global control-metric hypotheses (BB p. 382). -/
theorem exists_near_cutoff_lipschitz_constant {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) :
    ∃ L : ℝ, 0 < L ∧ ∀ ε : ℝ, 0 < ε →
      let χ := smoothQuasiballCutoff G ν 0 (ε / 2) ε
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ Measurable χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x, ε < ν x → χ x = 0) ∧
      (∀ x y, |χ x - χ y| ≤ (L / ε) * G2.gaugeDistance G Hc.norm x y) := by
  obtain ⟨B, hB, hb⟩ := exists_quasiball_cutoff_word_holder_semi_constants
    G H Hc ν hν (α := 1) (by norm_num)
  refine ⟨2 * B [], mul_pos (by norm_num) (hB []), ?_⟩
  intro ε hε
  dsimp only
  let χ := smoothQuasiballCutoff G ν 0 (ε / 2) ε
  have hhalf : 0 < ε / 2 := by positivity
  have hless : ε / 2 < ε := by linarith
  have hsm := smoothQuasiballCutoff_contDiff G ν hν 0 hhalf hless
  refine ⟨hsm, hsm.continuous.measurable, smoothQuasiballCutoff_compact G ν 0 hless,
    (fun x => smoothQuasiballCutoff_range G ν 0 x (ε / 2) ε), ?_, ?_⟩
  · intro x hx
    change quasiballProfile (ε / 2) ε (ν (G.mul (G.inv 0) x)) = 0
    rw [G2.inv_zero G, G2.zero_mul G]
    exact quasiballProfile_zero hless (by linarith)
  · let metric : MetricSpace (ControlCarrier N) :=
      gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
    have hn := hb [] 0 (ε / 2) ε hhalf hless le_rfl
    have he : B [] / (ε - ε / 2) = 2 * B [] / ε := by
      rw [show ε - ε / 2 = ε / 2 by ring, div_div_eq_mul_div]
      ring
    have hs : @H2.holderSemi (ControlCarrier N) metric 1 univ χ ≤
        ENNReal.ofReal (2 * B [] / ε) := by
      simpa only [wordDerivative, H1.differentialWordWeight, List.map_nil, List.sum_nil,
        Nat.cast_zero, zero_add, NNReal.coe_one, Real.rpow_one, he, χ] using hn
    have hfinite := hs.trans_lt ENNReal.ofReal_lt_top
    have hbound : (@H2.holderSemi (ControlCarrier N) metric 1 univ χ).toReal ≤
        2 * B [] / ε := by
      have hc : 0 ≤ 2 * B [] / ε :=
        div_nonneg (mul_nonneg (by norm_num) (hB []).le) hε.le
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
      rw [ENNReal.toReal_ofReal hc] at hh
      exact hh
    intro x y
    have hd := @H2.sub_le_holderSemi (ControlCarrier N) metric 1 univ χ
      hfinite x y (mem_univ x) (mem_univ y)
    simp only [NNReal.coe_one, Real.rpow_one] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right hbound dist_nonneg)

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory Filter
open scoped ENNReal Topology

/-- A uniform difference estimate transfers the Cauchy property without
requiring an operator to have been defined on the completed space. -/
theorem cauchySeq_of_difference_estimate {α β : Type*}
    [PseudoMetricSpace α] [PseudoMetricSpace β]
    (f : ℕ → α) (v : ℕ → β) (C : ℝ) (hC : 0 ≤ C)
    (hf : CauchySeq f)
    (hb : ∀ j l, dist (v j) (v l) ≤ C * dist (f j) (f l)) :
    CauchySeq v := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hCp : 0 < C + 1 := by linarith
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hf (ε / (C + 1)) (div_pos hε hCp)
  refine ⟨N, fun j hj l hl => ?_⟩
  have hd := hN j hj l hl
  have hsmall : (C + 1) * dist (f j) (f l) < ε := by
    simpa only [mul_comm] using (lt_div_iff₀ hCp).mp hd
  have hn := dist_nonneg (x := f j) (y := f l)
  have hbound := hb j l
  nlinarith

/-- The Young and singular-integral difference estimates imply
Lp Cauchy convergence of the classical jets (BB p. 374). -/
theorem lp_cauchy_of_difference_estimate {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : ℕ → α → ℝ) (v : ℕ → β → ℝ)
    (hf : ∀ j, MemLp (f j) p μ) (hv : ∀ j, MemLp (v j) p ν)
    (C : ℝ) (hC : 0 ≤ C)
    (hc : CauchySeq (fun j => (hf j).toLp (f j)))
    (hb : ∀ j l, eLpNorm (v j - v l) p ν ≤
      ENNReal.ofReal C * eLpNorm (f j - f l) p μ) :
    CauchySeq (fun j => (hv j).toLp (v j)) := by
  apply cauchySeq_of_difference_estimate _ _ C hC hc
  intro j l
  have he : edist ((hv j).toLp (v j)) ((hv l).toLp (v l)) ≤
      ENNReal.ofReal C * edist ((hf j).toLp (f j)) ((hf l).toLp (f l)) := by
    simpa only [Lp.edist_toLp_toLp] using hb j l
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (edist_ne_top _ _)) he
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ← dist_edist] using hr

end RothschildStein.H3

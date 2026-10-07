-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ExpandingCutoffWords
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace RothschildStein.H3

/-- Nonempty cutoff words produce vanishing Leibniz error terms against
any Lp function. No support assumption on the function is required. -/
theorem tendsto_expandingCutoff_word_mul_eLpNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (I : List (Fin (q+1))) (hI : I ≠ []) (x₀ : Fin N → ℝ)
    (μ : Measure (Fin N → ℝ)) {p : ℝ≥0∞}
    {f : (Fin N → ℝ) → ℝ} (hf : MemLp f p μ) :
    Tendsto (fun R : ℝ => eLpNorm
      (fun x => f x * wordDerivative H.fields I
        (smoothQuasiballCutoff G ν x₀ R (2*R)) x) p μ)
      atTop (𝓝 0) := by
  have ht := ENNReal.Tendsto.const_mul (a := eLpNorm f p μ)
    (tendsto_expandingCutoff_word_eLpNorm_top G H ν hν I hI x₀ μ)
    (Or.inr hf.eLpNorm_lt_top.ne)
  simp only [mul_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Filter.Eventually.of_forall fun _ => bot_le)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hm := (smoothQuasiballCutoff_word_contDiff G H ν hν I x₀ hR
    (by linarith : R < 2*R)).continuous.aestronglyMeasurable (μ := μ)
  have hb := eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top p hm (φ := f)
  have he : f • wordDerivative H.fields I (smoothQuasiballCutoff G ν x₀ R (2*R)) =
      (fun x => f x * wordDerivative H.fields I
        (smoothQuasiballCutoff G ν x₀ R (2*R)) x) := by
    funext x
    rfl
  rw [he] at hb
  exact hb

end RothschildStein.H3

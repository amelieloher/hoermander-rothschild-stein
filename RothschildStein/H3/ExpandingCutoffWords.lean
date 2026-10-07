-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffAllWords
public import RothschildStein.H3.CutoffWordLp
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace RothschildStein.H3

/-- Every nonempty ordered word of an expanding smooth gauge cutoff
converges uniformly to zero. The center and the measure are arbitrary. -/
theorem tendsto_expandingCutoff_word_eLpNorm_top {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (I : List (Fin (q+1))) (hI : I ≠ []) (x₀ : Fin N → ℝ)
    (μ : Measure (Fin N → ℝ)) :
    Tendsto (fun R : ℝ => eLpNorm
      (wordDerivative H.fields I (smoothQuasiballCutoff G ν x₀ R (2*R))) ⊤ μ)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_cutoff_all_word_constants G H ν hν
  have hw : H1.differentialWordWeight I ≠ 0 := by
    cases I with
    | nil => exact (hI rfl).elim
    | cons i J =>
      simp only [H1.differentialWordWeight, List.map_cons, List.sum_cons]
      split <;> omega
  have ht : Tendsto (fun R : ℝ => ENNReal.ofReal
      (C I * (R⁻¹) ^ H1.differentialWordWeight I)) atTop (𝓝 0) := by
    have ht := (tendsto_inv_atTop_zero.pow (H1.differentialWordWeight I)).const_mul (C I)
    simpa only [zero_pow hw, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Filter.Eventually.of_forall fun _ => bot_le)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hb := cutoff_word_eLpNorm_top_le_of_bound G H ν hν I x₀ hR
    (by linarith : R < 2*R) μ
    (hbound I hI x₀ R (2*R) hR (by linarith) (by linarith))
  simpa only [show 2*R-R=R by ring, div_eq_mul_inv, inv_pow] using hb

end RothschildStein.H3

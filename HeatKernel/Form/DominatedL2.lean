-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Dominated convergence in the L² seminorm

An almost everywhere convergent sequence with a common L² bound converges in the L²
seminorm. This applies to bounded scalar coefficients multiplying a fixed gradient.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace HeatKernel

/-- Almost everywhere convergence to zero with a common L² bound implies L² convergence. -/
theorem tendsto_eLpNorm_two_zero_of_dominated {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {f : ℕ → α → E} {b : α → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hb : MemLp b 2 μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ ‖b x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0) := by
  have hfin : (∫⁻ x, ‖b x‖ₑ ^ (2 : ℝ) ∂μ) ≠ ∞ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hb.eLpNorm_lt_top
    simpa using h.ne
  have ht := tendsto_lintegral_of_dominated_convergence'
    (fun x => ‖b x‖ₑ ^ (2 : ℝ))
    (fun n => (hf n).enorm.pow_const (2 : ℝ))
    (fun n => (hbound n).mono fun x hx =>
      ENNReal.rpow_le_rpow (by simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hx) (by norm_num : (0 : ℝ) ≤ 2))
    hfin (hlim.mono fun x hx => hx.enorm.ennrpow_const (2 : ℝ))
  have ht' := ht.ennrpow_const (1 / 2 : ℝ)
  simpa only [enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2),
    lintegral_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
    ht'.congr (fun n => by
      simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (hf n), ENNReal.toReal_ofNat])

end HeatKernel

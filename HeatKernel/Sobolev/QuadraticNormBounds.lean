-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! # Finite quadratic bounds and Lebesgue space representatives -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- A finite bound on the squared extended norm gives Lebesgue integrability. -/
theorem memLp_of_eLpNorm_sq_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {p C : ℝ≥0∞} {f : α → E}
    (hC : C ≠ ⊤) (h : eLpNorm f p μ ^ 2 ≤ C) : MemLp f p μ := by
  have hn : eLpNorm f p μ ^ 2 ≠ ⊤ := ne_top_of_le_ne_top hC h
  have hf : eLpNorm f p μ ≠ ⊤ := by simpa only [ENNReal.pow_ne_top_iff,
    OfNat.ofNat_ne_zero, or_false] using hn
  exact hf.lt_top

/-- Passing a squared extended norm bound to the ordinary norm of its representative. -/
theorem norm_toLp_sq_le_of_eLpNorm_sq_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞} {f : α → E}
    (hf : MemLp f p μ) {C : ℝ} (hC : 0 ≤ C)
    (h : eLpNorm f p μ ^ 2 ≤ ENNReal.ofReal C) : ‖hf.toLp f‖ ^ 2 ≤ C := by
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [Lp.norm_toLp, ENNReal.toReal_pow, ENNReal.toReal_ofReal hC] using ht

/-- A finite quadratic estimate produces an actual Lebesgue space element with a norm bound. -/
theorem exists_lp_of_eLpNorm_sq_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞} {f : α → E}
    {C : ℝ} (hC : 0 ≤ C) (h : eLpNorm f p μ ^ 2 ≤ ENNReal.ofReal C) :
    ∃ u : Lp E p μ, (⇑u =ᵐ[μ] f) ∧ ‖u‖ ≤ Real.sqrt C := by
  have hf := memLp_of_eLpNorm_sq_le ENNReal.ofReal_ne_top h
  exact ⟨hf.toLp f, hf.coeFn_toLp,
    Real.le_sqrt_of_sq_le (norm_toLp_sq_le_of_eLpNorm_sq_le hf hC h)⟩

end HeatKernel.Sobolev

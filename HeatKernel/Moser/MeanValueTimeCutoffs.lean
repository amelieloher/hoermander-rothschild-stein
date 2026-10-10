-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-! # Smooth lower-time cutoffs with a uniform derivative constant -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace HeatKernel

/-- The standard smooth transition has a bounded derivative on the whole real line. -/
theorem exists_smoothTransition_derivative_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv_one
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0 + 1, by positivity, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact (hC t ht).trans (by have := le_max_left C 0; linarith)
  · have hz : deriv Real.smoothTransition t = 0 := by
      rcases lt_or_ge t 0 with ht0 | h0t
      · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
          filter_upwards [eventually_lt_nhds ht0] with s hs
          exact Real.smoothTransition.zero_of_nonpos hs.le
        simpa only [deriv_const] using he.deriv_eq
      · have ht1 : 1 < t := by simp only [mem_Icc, not_and] at ht; exact lt_of_not_ge (ht h0t)
        have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
          filter_upwards [eventually_gt_nhds ht1] with s hs
          exact Real.smoothTransition.one_of_one_le hs.le
        simpa only [deriv_const] using he.deriv_eq
    rw [hz, norm_zero]
    positivity

/-- A smooth cutoff which vanishes before a lower time and equals one after an
interior lower time. It does not impose an upper-time boundary condition. -/
def lowerTimeCutoff (a b t : ℝ) : ℝ := Real.smoothTransition ((t - a) / (b - a))

/-- Lower-time cutoffs take values in the unit interval. -/
theorem lowerTimeCutoff_mem_Icc (a b t : ℝ) : lowerTimeCutoff a b t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The cutoff vanishes up to its initial lower time. -/
theorem lowerTimeCutoff_eq_zero {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    lowerTimeCutoff a b t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr ht) (sub_nonneg.mpr hab.le))

/-- The cutoff equals one from the interior lower time onward. -/
theorem lowerTimeCutoff_eq_one {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    lowerTimeCutoff a b t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)

/-- Every lower-time cutoff is smooth. -/
theorem contDiff_lowerTimeCutoff (a b : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (lowerTimeCutoff a b) := by
  unfold lowerTimeCutoff
  fun_prop

/-- The transition derivative constant is independent of both lower times. -/
theorem exists_uniform_lowerTimeCutoff_derivative_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, a < b → ∀ t : ℝ,
      ‖deriv (lowerTimeCutoff a b) t‖ ≤ C / (b - a) := by
  obtain ⟨C, hC, hbound⟩ := exists_smoothTransition_derivative_bound
  refine ⟨C, hC, fun a b hab t => ?_⟩
  have hd := ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
    ((t - a) / (b - a))).hasDerivAt.comp t
      (((hasDerivAt_id t).sub_const a).div_const (b - a))
  have he : deriv (lowerTimeCutoff a b) t =
      deriv Real.smoothTransition ((t - a) / (b - a)) * (1 / (b - a)) := by
    exact hd.deriv
  rw [he, norm_mul, Real.norm_of_nonneg (one_div_nonneg.mpr (sub_nonneg.mpr hab.le))]
  exact (mul_le_mul_of_nonneg_right (hbound _) (by positivity)).trans_eq (by ring)

end HeatKernel

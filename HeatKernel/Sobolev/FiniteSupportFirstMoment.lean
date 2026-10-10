-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-! # First moments of functions supported in a finite-volume set -/

@[expose] public section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HeatKernel.Sobolev

/-- The L¹ norm of an L² function supported in a set is controlled by its volume. -/
theorem eLpNorm_one_le_of_support_subset {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {f : α → E} {B : Set α}
    (hf : AEStronglyMeasurable f μ) (hsupport : Function.support f ⊆ B) :
    eLpNorm f 1 μ ≤ eLpNorm f 2 μ * μ B ^ (1 / 2 : ℝ) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hf.restrict (μ := μ.restrict B)
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, div_one,
    Measure.restrict_apply_univ] at h
  rw [eLpNorm_restrict_eq_of_support_subset hf hsupport,
    eLpNorm_restrict_eq_of_support_subset hf hsupport] at h
  exact h

/-- A finite support volume transfers L² integrability and its norm bound to L¹. -/
theorem memLp_one_and_toReal_le_of_support_subset {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {f : α → E} {B : Set α}
    (hf : MemLp f 2 μ) (hsupport : Function.support f ⊆ B) (hB : μ B ≠ ⊤) :
    MemLp f 1 μ ∧ (eLpNorm f 1 μ).toReal ≤
      (eLpNorm f 2 μ).toReal * (μ B).toReal ^ (1 / 2 : ℝ) := by
  have h := eLpNorm_one_le_of_support_subset hf.aestronglyMeasurable hsupport
  have ht : eLpNorm f 2 μ * μ B ^ (1 / 2 : ℝ) ≠ ⊤ := by
    finiteness
  refine ⟨(lt_of_le_of_lt h ht.lt_top), ?_⟩
  have hh := ENNReal.toReal_mono ht h
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] using hh

end HeatKernel.Sobolev

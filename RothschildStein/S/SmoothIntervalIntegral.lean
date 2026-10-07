-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactKernelIntegral
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric
open scoped Topology
namespace RothschildStein.S
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A joint smooth real function can be integrated smoothly over
[0,1] in its second variable (BB p. 76; Hadamard). -/
theorem contDiff_unitIntervalIntegral {k : P → ℝ → ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) (uncurry k)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ t in (0 : ℝ)..1, k x t) := by
  let ρ : ContDiffBump (0 : ℝ) := ⟨2,3,by norm_num,by norm_num⟩
  let g : P → ℝ → ℝ := fun x t => ρ t * k x t
  have hg : ContDiff ℝ (⊤ : ℕ∞) (uncurry g) :=
    (ρ.contDiff.comp contDiff_snd).mul hk
  have hgs : ∀ x t, x ∈ (univ : Set P) → t ∉ tsupport ρ → g x t = 0 := by
    intro x t _ ht
    change ρ t * k x t = 0
    rw [image_eq_zero_of_notMem_tsupport ht,MulZeroClass.zero_mul]
  have H := contDiffOn_compactKernelIntegral (μ := (volume : Measure ℝ))
    (h := (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)))
    isOpen_univ ρ.hasCompactSupport.isCompact hgs hg.contDiffOn
    ((locallyIntegrable_const (1 : ℝ)).indicator measurableSet_Ioc)
  rw [contDiffOn_univ] at H
  convert H using 1
  ext x
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  change (Ioc (0 : ℝ) 1).indicator (k x) t =
    (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t * g x t
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem ht,indicator_of_mem ht]
    have hρ : ρ t = 1 := ρ.one_of_mem_closedBall (by
      change dist t 0 ≤ 2
      rw [dist_zero_right,Real.norm_of_nonneg ht.1.le]
      linarith [ht.2])
    simp only [g,hρ,one_mul]
  · rw [indicator_of_notMem ht,indicator_of_notMem ht]
    simp only [MulZeroClass.zero_mul]

end RothschildStein.S

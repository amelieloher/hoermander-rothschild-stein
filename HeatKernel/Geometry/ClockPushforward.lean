-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Change of measure for increasing integral clocks. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory

namespace HeatKernel

/-- An increasing clock whose increments are integrals of a density transports Lebesgue
measure under its inverse to the weighted measure on the original interval. -/
theorem map_inverse_clock_eq_withDensity (e : ℝ ≃o ℝ) (w : ℝ → ℝ)
    (hw : IntegrableOn w (Icc 0 1))
    (hn : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), 0 ≤ w t)
    (he : ∀ t ∈ Icc (0 : ℝ) 1, e t = ∫ u in Icc (0 : ℝ) t, w u) :
    (volume.restrict (Icc (e 0) (e 1))).map e.symm =
      (volume.restrict (Icc (0 : ℝ) 1)).withDensity (fun t => ENNReal.ofReal (w t)) := by
  have hzero : e 0 = 0 := by simpa using he 0 (by norm_num)
  apply Measure.ext_of_Iic
  intro a
  rw [Measure.map_apply e.symm.continuous.measurable measurableSet_Iic,
    withDensity_apply _ measurableSet_Iic]
  have hp : e.symm ⁻¹' Iic a = Iic (e a) := by
    ext t
    simp only [mem_preimage, mem_Iic, e.symm_apply_le]
  rw [hp, Measure.restrict_apply measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  by_cases ha : a < 0
  · have hleft : Iic (e a) ∩ Icc (e 0) (e 1) = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      have hlt := e.strictMono ha
      grind
    have hright : Iic a ∩ Icc (0 : ℝ) 1 = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      grind
    simp [hleft, hright]
  · have ha0 : 0 ≤ a := le_of_not_gt ha
    by_cases ha1 : 1 ≤ a
    · have hleft : Iic (e a) ∩ Icc (e 0) (e 1) = Icc (e 0) (e 1) :=
        inter_eq_right.mpr (fun _ ht => ht.2.trans (e.monotone ha1))
      have hright : Iic a ∩ Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 :=
        inter_eq_right.mpr (fun _ ht => ht.2.trans ha1)
      rw [hleft, hright, Real.volume_Icc, hzero, sub_zero,
        ← ofReal_integral_eq_lintegral_ofReal hw hn, he 1 (by norm_num)]
    · have ha1' : a ≤ 1 := (lt_of_not_ge ha1).le
      have hleft : Iic (e a) ∩ Icc (e 0) (e 1) = Icc (e 0) (e a) := by
        ext t
        simp only [mem_inter_iff, mem_Iic, mem_Icc]
        have hle := e.monotone ha1'
        grind
      have hright : Iic a ∩ Icc (0 : ℝ) 1 = Icc (0 : ℝ) a := by
        ext t
        simp only [mem_inter_iff, mem_Iic, mem_Icc]
        grind
      have hsub : Icc (0 : ℝ) a ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc_right ha1'
      rw [hleft, hright, Real.volume_Icc, hzero, sub_zero,
        ← ofReal_integral_eq_lintegral_ofReal (hw.mono_set hsub)
          (ae_restrict_of_ae_restrict_of_subset hsub hn), he a ⟨ha0, ha1'⟩]

end HeatKernel

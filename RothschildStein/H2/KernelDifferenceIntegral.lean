-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.KernelTailBound
public import RothschildStein.H2.VolumeMeasurability
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Uniform L¹ tail of a second-variable kernel difference,
using the transposed smoothness constant and factor 4⁻ᵝ (BB p. 320). -/
theorem LocDoubling.kernel_difference_integral (D : LocDoubling X)
    {xbar z x : X} {R r β A S : ℝ} {K : X → X → ℝ}
    (hKt : KernelClass D.μ D.Ω₁ β 0 A S (fun x y => K y x))
    (hU : ball xbar R ⊆ D.Ω₁) (hR : R < D.κ)
    (hz : z ∈ D.Ω₁) (hx : x ∈ D.Ω₁)
    (hr : 0 < r) (hcap : 5 * r ≤ D.κ) (hxr : dist z x < r)
    (hsupport : ∀ a b, a ∉ ball xbar R ∨ b ∉ ball xbar R → K a b = 0) :
    (∫⁻ y in ball xbar R \ ball z (4 * r), ‖K y x - K y z‖ₑ ∂D.μ) ≤
      ENNReal.ofReal (S * volumeIntegralConstant D.C_D β * (4 : ℝ) ^ (-β)) := by
  let E := ball z (3 * D.κ) \ ball z (4 * r)
  let w : X → ℝ≥0∞ := fun y => ENNReal.ofReal (dist z y ^ (-β)) * (volumeAt D.μ z y)⁻¹
  let c := ENNReal.ofReal S * ENNReal.ofReal (r ^ β)
  have he3 : MeasurableSet (ball z (3 * D.κ)) := isOpen_ball.measurableSet
  have he4 : MeasurableSet (ball z (4 * r)) := isOpen_ball.measurableSet
  have hu : MeasurableSet (ball xbar R) := isOpen_ball.measurableSet
  have hE : MeasurableSet E := he3.diff he4
  have hw : Measurable w :=
    (((continuous_const.dist continuous_id).measurable.pow_const (-β)).ennreal_ofReal).mul
      (measurable_volumeAt D.μ z).inv
  have hbound : ∀ y ∈ ball xbar R \ ball z (4 * r),
      ‖K y x - K y z‖ₑ ≤ c * E.indicator w y := by
    intro y hy
    by_cases he : y ∈ E
    · rw [indicator_of_mem he]
      have hy₁ : y ∈ D.Ω₁ := hU hy.1
      have hd : dist z y ≤ 6 * D.κ := by
        have hh : dist z y < 3 * D.κ := by simpa only [mem_ball, dist_comm] using he.1
        linarith [D.κ_pos]
      have hyr : 4 * r ≤ dist z y := by simpa only [mem_ball, dist_comm, not_lt] using hy.2
      exact D.outerPatch.transpose_difference_enorm hKt hz hz hx hy₁ hr hxr hyr hd
    · have hz0 : K y x - K y z = 0 := by
        by_contra hn
        have hh := kernel_difference_distance_bound hR (by linarith : r ≤ D.κ / 5) hxr hsupport hn
        exact he ⟨by simpa only [mem_ball, dist_comm] using hh, hy.2⟩
      rw [hz0, enorm_zero]
      exact zero_le
  calc
    _ ≤ ∫⁻ y in ball xbar R \ ball z (4 * r), c * E.indicator w y ∂D.μ :=
      setLIntegral_mono' (hu.diff he4) hbound
    _ ≤ ∫⁻ y, c * E.indicator w y ∂D.μ := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = c * ∫⁻ y in E, w y ∂D.μ := by
      rw [lintegral_const_mul'' c (hw.indicator hE).aemeasurable, lintegral_indicator hE]
    _ ≤ ENNReal.ofReal S * ENNReal.ofReal (volumeIntegralConstant D.C_D β * (4 : ℝ) ^ (-β)) := by
      rw [mul_assoc]
      exact mul_le_mul' le_rfl (D.outerPatch.scaled_outer_volume_integral hz hKt.β_pos hr
        (by linarith [D.κ_pos]) (by change 3 * D.κ ≤ 6 * D.κ; linarith [D.κ_pos]))
    _ = _ := by rw [← ENNReal.ofReal_mul hKt.S_nonneg]; congr 1; ring

end RothschildStein.H2

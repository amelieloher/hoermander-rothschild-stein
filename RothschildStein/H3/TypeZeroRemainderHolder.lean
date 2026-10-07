-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroRemainderClass
public import RothschildStein.H3.GroupSetting
public import RothschildStein.H2.KernelRestriction
public import RothschildStein.H2.FractionalHolderNorm
public import RothschildStein.H2.PrincipalValueLimits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric MeasureTheory
open scoped NNReal ENNReal
namespace RothschildStein.H3

/-- The actual nonsingular remainder on the unit ball has a
uniform Hölder bound linear in the type-zero kernel's first seminorm. -/
theorem exists_typeZero_remainder_holder_bound_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N)
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (C : G2.ControlNormConclusion G driftWeight Y)
    (hY : ∀ i, ContinuousOn (Y i) {0}ᶜ)
    (hhomY : ∀ i, G2.IsHomogeneousField G (Y i) (if i = 0 then 2 else 1))
    {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1) :
    let _metric := gaugeMetric G C.norm C.constant_one C.symmetric
    let E := ball (0 : ControlCarrier N) 1
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (k : (Fin N → ℝ) → ℝ), TypeZero G C.norm k →
      ∀ (F : ControlCarrier N → ℝ), H2.BoundedHolder a E F →
      H2.boundedHolderNorm a E
        (H2.fractionalIntegral volume E
          (fun x y => cutoffGroupKernel G (typeZeroRemainderCutoff C.norm) k x y) F) ≤
        ENNReal.ofReal (kernelDerivativeBound C.norm k 1 * B) * H2.boundedHolderNorm a E F := by
  let _metric := gaugeMetric G C.norm C.constant_one C.symmetric
  let E := ball (0 : ControlCarrier N) 1
  let D := groupSetting G C.norm C.constant_one C.symmetric
  let m := (volume {z : Fin N → ℝ | C.norm z < 1}).toReal
  let S := cutoffKernelSmoothConstant C.norm Y (-(G.homogeneousDimension : ℝ)) 3 2
  let J := H2.fractionalHolderConstant D.C_D D.κ 2 a 1
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  have hS : 0 ≤ S := cutoffKernelSmoothConstant_nonneg C.norm Y
    (-(G.homogeneousDimension : ℝ)) (by norm_num) (by norm_num)
  have hJ : 0 ≤ J := by
    have hsemi := H2.fractionalSemiConstant_nonneg (C := D.C_D)
      (by linarith [D.one_lt_C_D]) D.κ_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1) ha1
    have hvol := (H2.volumeIntegralConstant_pos
      (C := D.C_D) (by linarith [D.one_lt_C_D]) (by norm_num : (0 : ℝ) < 1)).le
    exact add_nonneg hsemi (mul_nonneg hvol (Real.rpow_nonneg (by norm_num) _))
  dsimp only
  refine ⟨J * (m + 2 * (m * S)), mul_nonneg hJ (by positivity), ?_⟩
  intro k hk F hf
  let Λ := kernelDerivativeBound C.norm k 1
  let K := fun x y : ControlCarrier N => cutoffGroupKernel G (typeZeroRemainderCutoff C.norm) k x y
  have hclass := typeZero_remainder_fractional_class_of_controlNorm G C hY hhomY hk
  have hK : H2.SupportedKernel D E E 1 1 (m * Λ) (2 * (m * S * Λ)) 2 K := by
    refine ⟨isOpen_ball.measurableSet, subset_rfl, ?_, by norm_num, ?_,
      hclass.restrict isOpen_ball.measurableSet (subset_univ _), ?_⟩
    · change ball (0 : ControlCarrier N) 1 ⊆ ball 0 19
      exact ball_subset_ball (by norm_num)
    · change (2 : ℝ) ≤ 3 * 3
      norm_num
    · intro x hx y hy hxy
      have ht := dist_triangle x 0 y
      have hx' : dist x 0 < 1 := hx
      have hy' : dist y 0 < 1 := hy
      rw [dist_comm 0 y] at ht
      exfalso
      linarith
  let M := (H2.boundedHolderNorm a E F).toReal
  have hfb : ∀ᵐ y ∂volume.restrict E, |F y| ≤ M := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with y hy
    exact (H2.abs_le_holderSup hf.parts.1 hy).trans
      (ENNReal.toReal_mono hf.ne (le_add_right le_rfl))
  have hb := hK.fractional_holder_norm_le ha ha1.le ha1
    (hf.aestronglyMeasurable_restrict ha isOpen_ball.measurableSet)
    (M := M) ENNReal.toReal_nonneg hfb
  have hcoeff : J * (m * Λ + 2 * (m * S * Λ)) * M =
      (Λ * (J * (m + 2 * (m * S)))) * M := by ring
  change H2.boundedHolderNorm a E (H2.fractionalIntegral volume E K F) ≤
    ENNReal.ofReal (Λ * (J * (m + 2 * (m * S)))) * H2.boundedHolderNorm a E F
  change H2.boundedHolderNorm a E (H2.fractionalIntegral volume E K F) ≤
    ENNReal.ofReal (J * (m * Λ + 2 * (m * S * Λ)) * M) at hb
  rw [hcoeff, ENNReal.ofReal_mul
    (mul_nonneg (kernelDerivativeBound_properties C.norm.gauge hk.smooth 1).1
      (mul_nonneg hJ (by positivity))), ENNReal.ofReal_toReal hf.ne] at hb
  exact hb

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.KernelEnormIncrement
public import RothschildStein.S.KernelTonelliBound
public import RothschildStein.S.LpPowerMoments
public import RothschildStein.S.TranslationModulus
public import RothschildStein.S.FriedrichsInteriorPatch

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric Filter TopologicalSpace
open scoped ENNReal Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exact finite-p translation-modulus bound for a smooth
zero-mean kernel on an interior patch. Jensen and Tonelli cover p=1
without a separate limiting argument (BB Lemma 2.11, p. 74). -/
theorem eLpNorm_smoothFriedrichsKernelOp_le_modulus
    (Ω : Opens (Fin n → ℝ)) (K : SmoothFriedrichsKernel n)
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hc : IsCompact (closure U))
    {δ ε : ℝ} (hε : ε ∈ Ioo 0 δ) (hδ : cthickening δ (closure U) ⊆ Ω)
    (hpt : p ≠ ⊤) (f : Lp ℝ p (volume : Measure (Fin n → ℝ)))
    (C : ℝ) (hsize : ∀ x ∈ U, ∀ y, ‖K.family ε x y‖ ≤ C)
    (hmean : ∀ x ∈ U, (∫ y, K.family ε x y) = 0) :
    eLpNorm (friedrichsKernelOp K.family f ε) p (volume.restrict U) ≤
      ENNReal.ofReal C * volume (closedBall (0 : Fin n → ℝ) 1) * translationModulus f ε := by
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hpt (Fact.out : 1 ≤ p)
  have hp0 : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hp1
  have hpz : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hloc : LocallyIntegrableOn (⇑f) (Ω : Set (Fin n → ℝ)) volume :=
    ((Lp.memLp f).locallyIntegrable Fact.out).locallyIntegrableOn _
  let F := fun x y : Fin n → ℝ => ‖f (x+ε • y)-f x‖ₑ
  have hm : Measurable (uncurry F) := by
    have ht : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => z.1+ε • z.2) :=
      continuous_fst.add (continuous_snd.const_smul ε)
    exact (((Lp.stronglyMeasurable f).measurable.comp ht.measurable).sub
      ((Lp.stronglyMeasurable f).measurable.comp measurable_fst)).enorm
  have hQ : ∀ᵐ x ∂volume.restrict U, ‖friedrichsKernelOp K.family f ε x‖ₑ ≤
      ENNReal.ofReal C * ∫⁻ y in closedBall (0 : Fin n → ℝ) 1, F x y := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact enorm_smoothFriedrichsKernelOp_le_increment Ω K hloc hε.1 x
      ((closedBall_subset_closedBall hε.2.le).trans
        (closedBall_subset_of_interior_thickening Ω hδ hx))
      (hmean x hx) C (hsize x hx)
  have hM : ∀ᵐ y ∂volume.restrict (closedBall (0 : Fin n → ℝ) 1),
      (∫⁻ x in U, (F x y)^p.toReal) ≤ (translationModulus f ε)^p.toReal := by
    filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with y hy
    have hb : ‖ε • y‖ ≤ ε := by
      rw [norm_smul,Real.norm_of_nonneg hε.1.le]
      have hy' : ‖y‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hy
      exact mul_le_of_le_one_right hε.1.le hy'
    have ht : AEStronglyMeasurable (fun x => f (x+ε • y)-f x) volume :=
      ((Lp.memLp f).aestronglyMeasurable.comp_measurePreserving
        (measurePreserving_add_right volume (ε • y))).sub (Lp.memLp f).aestronglyMeasurable
    calc
      _ ≤ ∫⁻ x, ‖f (x+ε • y)-f x‖ₑ^p.toReal :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ = (eLpNorm (fun x => f (x+ε • y)-f x) p volume)^p.toReal :=
        lintegral_enorm_rpow_eq_eLpNorm_rpow hpz hpt ht
      _ ≤ _ := ENNReal.rpow_le_rpow (translation_increment_le_modulus f ε (ε • y) hb) hp0.le
  have H := lintegral_kernelEnvelope_rpow_le (μ := volume.restrict U)
    (ν := volume.restrict (closedBall (0 : Fin n → ℝ) 1)) hm hp1 hQ hM
  simp only [Measure.restrict_apply_univ] at H
  rw [kernelMoment_factors_eq_rpow _ _ _ hp1] at H
  have H' := ENNReal.rpow_le_rpow H (one_div_pos.mpr hp0).le
  rw [← ENNReal.rpow_mul,mul_one_div_cancel hp0.ne',ENNReal.rpow_one] at H'
  have ho : AEStronglyMeasurable (friedrichsKernelOp K.family f ε) (volume.restrict U) :=
    (contDiffOn_friedrichsKernelOp_interior_patch Ω K hU hc hε.1 hε.2 hδ hloc).continuousOn.aestronglyMeasurable
      hU.measurableSet
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpz hpt ho]
  exact H'

end RothschildStein.S

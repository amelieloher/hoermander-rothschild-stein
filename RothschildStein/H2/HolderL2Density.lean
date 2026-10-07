-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderModule
public import RothschildStein.H2.HolderDensity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The concrete Hölder module has dense image in L²(U).
The bounded Lipschitz approximation supplies the density step. -/
theorem holderL2_denseRange {μ : Measure X} {δ : ℝ≥0} {U : Set X}
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hμ : μ U < ⊤) : DenseRange (holderL2 δ U μ hδ hU.measurableSet hμ) := by
  rw [Metric.denseRange_iff]
  intro v ε hε
  obtain ⟨g, he, hg⟩ := exists_boundedHolder_on_open hU hUb hμ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hδ₁ (Lp.memLp v) hε
  let f := holderNormalize hg
  let w := holderL2 δ U μ hδ hU.measurableSet hμ f
  have hw : (w : X → ℝ) =ᵐ[μ.restrict U] g := by
    have ht := (f.property.1.memLp_two hδ hU.measurableSet hμ).coeFn_toLp
    filter_upwards [ht, ae_restrict_mem hU.measurableSet] with x hx hxu
    exact hx.trans (indicator_of_mem hxu g)
  have hn : eLpNorm (fun x => v x - w x) 2 (μ.restrict U) < ENNReal.ofReal ε := by
    refine (eLpNorm_congr_ae ?_).trans_lt he
    filter_upwards [hw] with x hx
    simp only [hx, Pi.sub_apply]
  refine ⟨f, ?_⟩
  change dist v w < ε
  rw [dist_eq_norm_sub, Lp.norm_def]
  have heq : eLpNorm (v - w) 2 (μ.restrict U) = eLpNorm (fun x => v x - w x) 2 (μ.restrict U) :=
    eLpNorm_congr_ae (Lp.coeFn_sub v w)
  rw [heq]
  exact (ENNReal.toReal_lt_toReal hn.ne_top ENNReal.ofReal_ne_top).mpr hn |>.trans_eq
    (ENNReal.toReal_ofReal hε.le)

/-- The L² norm is dominated by the auxiliary Hölder seminorm. -/
theorem holderL2_norm_le {μ : Measure X} {δ : ℝ≥0} {U : Set X}
    (hδ : 0 < δ) (hU : MeasurableSet U) (hμ : μ U < ⊤) (f : holderFunctions δ U) :
    ‖holderL2 δ U μ hδ hU hμ f‖ ≤
      (μ U ^ (1 / 2 : ℝ)).toReal * holderFunctionSeminorm δ U f := by
  have hm := f.property.1.memLp_two hδ hU hμ
  have hb : ∀ᵐ x ∂μ.restrict U, ‖(f : X → ℝ) x‖ ≤ (boundedHolderNorm δ U f).toReal := by
    filter_upwards [ae_restrict_mem hU] with x hx
    refine (abs_le_holderSup f.property.1.parts.1 hx).trans ?_
    exact ENNReal.toReal_mono f.property.1.ne (le_add_right le_rfl)
  have he := eLpNorm_le_of_ae_bound (p := 2) hm.aestronglyMeasurable hb
  simp only [Measure.restrict_apply_univ, ENNReal.toReal_ofNat] at he
  rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num] at he
  have ht : μ U ^ (1 / 2 : ℝ) * ENNReal.ofReal (boundedHolderNorm δ U f).toReal ≠ ⊤ := by
    finiteness
  have hr := ENNReal.toReal_mono ht he
  change ‖hm.toLp (f : X → ℝ)‖ ≤ _
  rw [Lp.norm_toLp]
  change (eLpNorm (f : X → ℝ) 2 (μ.restrict U)).toReal ≤
    (μ U ^ (1 / 2 : ℝ)).toReal * (boundedHolderNorm δ U f).toReal
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ENNReal.toReal_nonneg] using hr

end RothschildStein.H2

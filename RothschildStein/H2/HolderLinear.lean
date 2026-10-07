-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderOperations
public import RothschildStein.H2.PrincipalValueLimits
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Absolute homogeneity of the auxiliary Hölder norm. -/
theorem boundedHolderNorm_smul {δ : ℝ≥0} {U : Set X} (c : ℝ) (f : X → ℝ) :
    boundedHolderNorm δ U (c • f) = ENNReal.ofReal |c| * boundedHolderNorm δ U f := by
  unfold boundedHolderNorm holderSup holderSemi
  have hs : (⨆ x : U, ENNReal.ofReal |(c • f) x|) =
      ENNReal.ofReal |c| * ⨆ x : U, ENNReal.ofReal |f x| := by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, ENNReal.ofReal_mul (abs_nonneg c)]
    rw [ENNReal.mul_iSup]
  rw [hs]
  have hh : eHolderNorm δ (fun x : U => (c • f) x) =
      ENNReal.ofReal |c| * eHolderNorm δ (fun x : U => f x) := by
    have he := eHolderNorm_smul (r := δ) (f := fun x : U => f x) c
    rw [← ENNReal.ofReal_coe_nnreal] at he
    have hfun : (fun x : U => (c • f) x) = c • (fun x : U => f x) := by
      funext x
      rfl
    rw [hfun]
    simpa only [coe_nnnorm, Real.norm_eq_abs] using he
  rw [hh, mul_add]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Scalar multiplication preserves the dense Hölder class. -/
theorem BoundedHolder.smul {δ : ℝ≥0} {U : Set X} {f : X → ℝ}
    (hf : BoundedHolder δ U f) (c : ℝ) : BoundedHolder δ U (c • f) := by
  unfold BoundedHolder
  rw [boundedHolderNorm_smul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf

omit [MeasurableSpace X] [BorelSpace X] in
/-- Zero belongs to every bounded Hölder space. -/
theorem boundedHolder_zero (δ : ℝ≥0) (U : Set X) : BoundedHolder δ U (0 : X → ℝ) := by
  simp [BoundedHolder, boundedHolderNorm, holderSup, holderSemi]

/-- The dense Hölder class embeds into L² on a finite-measure patch. -/
theorem BoundedHolder.memLp_two {μ : Measure X} {δ : ℝ≥0} {U : Set X} {f : X → ℝ}
    (hf : BoundedHolder δ U f) (hδ : 0 < δ) (hU : MeasurableSet U)
    (hμ : μ U < ⊤) : MemLp f 2 (μ.restrict U) := by
  let : IsFiniteMeasure (μ.restrict U) := ⟨by simpa using hμ⟩
  exact MemLp.of_bound (hf.aestronglyMeasurable_restrict hδ hU) (holderSup U f).toReal
    (by filter_upwards [ae_restrict_mem hU] with x hx
        simpa only [Real.norm_eq_abs] using abs_le_holderSup hf.parts.1 hx)

end RothschildStein.H2

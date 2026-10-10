-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.RealL2Subspace
public import HeatKernel.Semigroup.ComplexL2Positivity
public import HeatKernel.Semigroup.PositiveResolventSpectrum
public import HeatKernel.Semigroup.RealHeatOperators

/-! # Heat operators on real L²

Complex functional calculus, restricted to the closed real subspace, gives strongly
continuous contractive heat operators for every positive injective real contraction.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HeatKernel
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hpos : R.IsPositive) (hnorm : ‖R‖ ≤ 1)

/-- The heat operator on the canonical closed real subspace. -/
def realL2SubspaceHeatOperator (t : ℝ≥0) : realL2Subspace μ →L[ℝ] realL2Subspace μ :=
  realHeatOperator (realL2Subspace μ) (isClosed_realL2Subspace μ) (complexL2Extension μ R)
    (complexL2Extension_isSelfAdjoint μ R hpos.isSelfAdjoint)
    (mapsTo_complexL2Extension_realL2Subspace μ R)
    (spectrum_subset_Icc_of_isPositive_norm_le_one _ (complexL2Extension_isPositive μ R hpos)
      (norm_complexL2Extension_le_one μ R hnorm)) t

/-- The real L² heat operator, transported from the complex functional calculus. -/
def realL2HeatOperator (t : ℝ≥0) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (realL2SubspaceEquiv μ).symm.toContinuousLinearMap.comp
    ((realL2SubspaceHeatOperator μ R hpos hnorm t).comp
      (realL2SubspaceEquiv μ).toContinuousLinearMap)

theorem l2OfReal_realL2HeatOperator (t : ℝ≥0) (f : Lp ℝ 2 μ) :
    l2OfReal μ (realL2HeatOperator μ R hpos hnorm t f) =
      heatOperator (complexL2Extension μ R) t (l2OfReal μ f) := by
  have he := (realL2SubspaceEquiv μ).apply_symm_apply
    (realL2SubspaceHeatOperator μ R hpos hnorm t (realL2SubspaceEquiv μ f))
  exact congrArg (fun y : realL2Subspace μ => (y : Lp ℂ 2 μ)) he

theorem realL2HeatOperator_isSelfAdjoint (t : ℝ≥0) :
    IsSelfAdjoint (realL2HeatOperator μ R hpos hnorm t) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  have hs : inner ℂ (heatOperator (complexL2Extension μ R) t (l2OfReal μ f))
      (l2OfReal μ g) = inner ℂ (l2OfReal μ f)
      (heatOperator (complexL2Extension μ R) t (l2OfReal μ g)) :=
    (heatOperator_isSelfAdjoint (complexL2Extension μ R) t).isSymmetric _ _
  rw [← l2OfReal_realL2HeatOperator μ R hpos hnorm t f,
    ← l2OfReal_realL2HeatOperator μ R hpos hnorm t g, inner_l2OfReal, inner_l2OfReal] at hs
  exact Complex.ofReal_injective hs

theorem realL2SubspaceHeatOperator_zero : realL2SubspaceHeatOperator μ R hpos hnorm 0 = 1 :=
  realHeatOperator_zero _ _ _ _ _ _

theorem realL2SubspaceHeatOperator_add (s t : ℝ≥0) :
    realL2SubspaceHeatOperator μ R hpos hnorm (s + t) =
      realL2SubspaceHeatOperator μ R hpos hnorm s *
        realL2SubspaceHeatOperator μ R hpos hnorm t := realHeatOperator_add _ _ _ _ _ _ s t

theorem realL2HeatOperator_zero : realL2HeatOperator μ R hpos hnorm 0 = 1 := by
  ext1 f
  simp only [realL2HeatOperator, ContinuousLinearMap.comp_apply,
    realL2SubspaceHeatOperator_zero, one_apply_eq_self,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

theorem realL2HeatOperator_add (s t : ℝ≥0) :
    realL2HeatOperator μ R hpos hnorm (s + t) =
      realL2HeatOperator μ R hpos hnorm s * realL2HeatOperator μ R hpos hnorm t := by
  ext1 f
  simp only [realL2HeatOperator, ContinuousLinearMap.comp_apply,
    realL2SubspaceHeatOperator_add, mul_apply_eq_comp,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

theorem norm_realL2HeatOperator_le_one (t : ℝ≥0) :
    ‖realL2HeatOperator μ R hpos hnorm t‖ ≤ 1 := by
  have he (y : realL2Subspace μ) : ‖(realL2SubspaceEquiv μ).symm y‖ = ‖y‖ := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      (norm_realL2SubspaceEquiv μ ((realL2SubspaceEquiv μ).symm y)).symm
  have ht : ‖realL2SubspaceHeatOperator μ R hpos hnorm t‖ ≤ 1 :=
    norm_realHeatOperator_le _ _ _ _ _ _ t
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖(realL2SubspaceEquiv μ).symm
    (realL2SubspaceHeatOperator μ R hpos hnorm t (realL2SubspaceEquiv μ f))‖ ≤ _
  rw [he, one_mul]
  calc
    _ ≤ ‖realL2SubspaceHeatOperator μ R hpos hnorm t‖ * ‖realL2SubspaceEquiv μ f‖ :=
      (realL2SubspaceHeatOperator μ R hpos hnorm t).le_opNorm _
    _ ≤ ‖f‖ := by
      rw [norm_realL2SubspaceEquiv]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht (norm_nonneg f)

theorem continuous_realL2HeatOperator_apply (hinj : Function.Injective R) (f : Lp ℝ 2 μ) :
    Continuous (fun t : ℝ≥0 => realL2HeatOperator μ R hpos hnorm t f) := by
  have hc : Continuous (fun t : ℝ≥0 =>
      realL2SubspaceHeatOperator μ R hpos hnorm t (realL2SubspaceEquiv μ f)) :=
    continuous_realHeatOperator_apply_of_denseRange _ _ _ _ _ _
      (denseRange_complexL2Extension μ R hpos.isSelfAdjoint hinj) _
  exact (realL2SubspaceEquiv μ).symm.continuous.comp hc

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueMatrixCutoffPair
public import HeatKernel.Moser.MeanValueSmoothSpatialWeights
public import HeatKernel.Moser.MeanValueMatrixSobolevEnergy
public import HeatKernel.Moser.MeanValueSobolevEnergyMoments
public import HeatKernel.Moser.MeanValuePowerMomentRepresentatives
public import HeatKernel.Moser.MeanValueSignedMatrixPowerMoment
public import HeatKernel.Moser.MeanValueNestedPowerCutoffs
public import HeatKernel.Moser.MeanValueNestedPowerNorms
public import HeatKernel.Moser.MeanValueTimeCutoffs
public import HeatKernel.Moser.MeanValueUnitPowerStepBounds
public import HeatKernel.Moser.MeanValueSignedMatrixUnitPowerStep
public import HeatKernel.Moser.MeanValueFiniteIteration
public import HeatKernel.Moser.MeanValueEnergyFactors
public import HeatKernel.Moser.MeanValueCutoffRadii
public import HeatKernel.Moser.MeanValueGapExponent
public import HeatKernel.Moser.MeanValueSignedMatrixUnitGapBounds
public import HeatKernel.Bridge.ParabolicValueIntegrability
public import HeatKernel.Geometry.CoordinateBall
import Mathlib.Tactic

/-! # Finite bounds on compactly truncated unit cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- The weak quadratic mean-value estimate and compact local energy give one
finite essential bound for all radii in a fixed interior range. Its size may
depend on the solution and terminal time; small-power absorption removes it. -/
theorem exists_signed_matrix_unit_interior_uniform_essential_bound {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper)
    {u : ℝ → (Fin N → ℝ) → ℝ}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan
      coeff ⟨Ioo (-1 : ℝ) 0, isOpen_Ioo⟩
      (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1) u)
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j))
    (hbound : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2)
    {b : ℝ} (hbLow : -1 / 16 ≤ b) (hb : b < 0) :
    ∃ H : ℝ, ∀ r ∈ Icc (1 / 2 : ℝ) (3 / 4),
      eLpNormEssSup (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2)
        ((volume.restrict (Icc (-r) b)).prod (volume.restrict
          (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) r : Set (Fin N → ℝ)))) ≤
        ENNReal.ofReal H := by
  let ν := max 2 (G.homogeneousDimension : ℝ) + 1
  obtain ⟨C, hC, hgap⟩ := exists_uniform_signed_matrix_unit_gap_essential_bound
    G hq hqpos hspan hw (ν := ν) (by dsimp only [ν]; linarith) ell upper hell hupper
  let x₀ : CarnotPoint G hq hqpos hspan := (0 : Fin N → ℝ)
  let _ : ProperSpace (CarnotPoint G hq hqpos hspan) :=
    CarnotPoint.properSpace G hq hqpos hspan hw
  let K : Set (Fin N → ℝ) := @Metric.closedBall (CarnotPoint G hq hqpos hspan) _ x₀ (7 / 8)
  let f := fun z : ℝ × (Fin N → ℝ) => u z.1 z.2
  let μ := fun r : ℝ => (volume.restrict (Icc (-r) b)).prod (volume.restrict
    (CarnotPoint.coordinateBall G hq hqpos hspan x₀ r : Set (Fin N → ℝ)))
  have hJI : Icc (-(7 / 8 : ℝ)) b ⊆ Ioo (-1 : ℝ) 0 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hKU : K ⊆ (CarnotPoint.coordinateBall G hq hqpos hspan x₀ 1 : Set (Fin N → ℝ)) :=
    Metric.closedBall_subset_ball (α := CarnotPoint G hq hqpos hspan) (by norm_num)
  have hm := hu.memLp_two_on_compact_cylinder G hq hqpos hw hspan
    coeff ⟨Ioo (-1 : ℝ) 0, isOpen_Ioo⟩
    (CarnotPoint.coordinateBall G hq hqpos hspan x₀ 1)
    isCompact_Icc hJI (isCompact_closedBall x₀ (7 / 8)) hKU
  have hf : MemLp f 2 (μ (7 / 8)) := by
    dsimp only [μ]
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hm.mono_measure (Measure.restrict_mono
      (prod_mono Subset.rfl (Metric.ball_subset_closedBall (α := CarnotPoint G hq hqpos hspan))) le_rfl)
  have hbound := hgap u coeff hu ha hbound b hbLow hb (3 / 4) (7 / 8)
    (by norm_num) (by norm_num) (by norm_num)
  let B := ENNReal.ofReal (C * ((7 / 8 : ℝ) - 3 / 4) ^ (-(1 + ν / 2))) *
    eLpNorm f 2 (μ (7 / 8))
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  refine ⟨B.toReal, ?_⟩
  intro r hr
  rw [ENNReal.ofReal_toReal hB]
  have hmono : μ r ≤ μ (3 / 4) := Measure.prod_mono
    (Measure.restrict_mono (Icc_subset_Icc (neg_le_neg hr.2) le_rfl) le_rfl)
    (Measure.restrict_mono
      (Metric.ball_subset_ball (α := CarnotPoint G hq hqpos hspan) hr.2) le_rfl)
  exact (eLpNormEssSup_mono_measure f (Measure.absolutelyContinuous_of_le hmono)).trans hbound

end HeatKernel

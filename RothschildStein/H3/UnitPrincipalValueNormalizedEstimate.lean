-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.UnitLocalPrincipalValueIdentification
public import RothschildStein.H3.NormalizedPrincipalValueNonnegative
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory Filter
open scoped NNReal ENNReal Topology
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The unit-ball type-zero estimate follows from the proved local H2
operator and the finite tail Young bound, with constants independent of u and linear in the kernel seminorm. -/
theorem unitPrincipalValue_normalized_eLpNorm_bound_of_truncatedKernelFacts (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (A S : ℝ)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (k : ControlCarrier N → ℝ)
    (H : let _metric := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume (Λ * A) (Λ * S) (fun x y : ControlCarrier N => truncatedKernel G ν k x y))
    (Ht : let _metric := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume (Λ * A) (Λ * S) (fun x y : ControlCarrier N => truncatedKernel G ν k y x))
    (hk : TypeZero G ν k) (hSphere : kernelSphereBound ν k ≤ Λ) {p : ℝ} (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (u : ControlCarrier N → ℝ) (hu : ContDiff ℝ 1 (fun y : Fin N → ℝ => u y))
    (hs : HasCompactSupport u) (hsu : ∀ y, 1 ≤ ν y → u y = 0)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    (hf : let _metric := gaugeMetric G ν h1 hsym
      H2.BoundedHolder δ (ball (0 : ControlCarrier N) 2) u) :
    let _metric := gaugeMetric G ν h1 hsym
    let _Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym (Λ * A) (Λ * S) (truncatedKernel G ν k) H
    eLpNorm (fun x : ControlCarrier N => H1.principalValueConvolution G ν k u x)
        (ENNReal.ofReal p) (volume.restrict (ball 0 1)) ≤
      (ENNReal.ofReal (Λ * normalizedLocalLpConstant G ν h1 hsym A S hA hS p) +
        ENNReal.ofReal Λ * volume {x | 1 ≤ ν x ∧ ν x ≤ 2}) *
          eLpNorm u (ENNReal.ofReal p) volume := by
  let _metric := gaugeMetric G ν h1 hsym
  let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym (Λ * A) (Λ * S) (truncatedKernel G ν k) H
  let C := ENNReal.ofReal (Λ * normalizedLocalLpConstant G ν h1 hsym A S hA hS p)
  let B := ENNReal.ofReal Λ * volume {x | 1 ≤ ν x ∧ ν x ≤ 2}
  dsimp only
  obtain ⟨Tp, _, hbound⟩ := normalizedPrincipalValue_nonnegative_of_truncatedKernelFacts G ν h1 hsym A S
    hA hS Λ hΛ (truncatedKernel G ν k) H Ht hp
  have hlocal := (hbound δ hδ hδ1 u hf).2.1
  have hloc : eLpNorm (Q.principalValue u) (ENNReal.ofReal p) (volume.restrict (ball 0 1)) ≤
      C * eLpNorm u (ENNReal.ofReal p) volume := by
    calc
      _ ≤ eLpNorm (Q.principalValue u) (ENNReal.ofReal p) (volume.restrict (ball 0 2)) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono_set volume (ball_subset_ball (by norm_num)))
      _ ≤ C * eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball 0 2)) := hlocal
      _ ≤ _ := mul_le_mul' le_rfl (eLpNorm_mono_measure _ Measure.restrict_le_self)
  have huLp : MemLp (fun y : Fin N → ℝ => u y) (ENNReal.ofReal p) volume :=
    hu.continuous.memLp_of_hasCompactSupport hs
  have ht := (hk.unitTail_convolution_memLp_and_bound G Fact.out huLp).2
  have hcoef : ENNReal.ofReal (kernelSphereBound ν k) * volume {x | 1 ≤ ν x ∧ ν x ≤ 2} ≤ B :=
    mul_le_mul' (ENNReal.ofReal_le_ofReal hSphere) le_rfl
  have ht' := ht.trans (mul_le_mul' hcoef le_rfl)
  have htail : eLpNorm (fun x : ControlCarrier N => G2.groupConvolution G u (typeZeroUnitTail ν k) x)
      (ENNReal.ofReal p) (volume.restrict (ball 0 1)) ≤ B * eLpNorm u (ENNReal.ofReal p) volume :=
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ht'
  have he : (fun x : ControlCarrier N => H1.principalValueConvolution G ν k u x)
      =ᵐ[volume.restrict (ball 0 1)] Q.principalValue u +
        (fun x : ControlCarrier N => G2.groupConvolution G u (typeZeroUnitTail ν k) x) := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
    have hnx : ν x < 1 := by
      change dist x 0 < 1 at hx
      rwa [gaugeMetric_dist_zero G ν h1 hsym x] at hx
    have h := localKernelData_unit_source_principalValue G ν h1 hsym (Λ * A) (Λ * S) k u H hk hu hs hsu hδ hδ1 hf hnx
    change H1.principalValueConvolution G ν k u x = Q.principalValue u x + _
    linarith
  rw [eLpNorm_congr_ae he]
  calc
    _ ≤ eLpNorm (Q.principalValue u) (ENNReal.ofReal p) (volume.restrict (ball 0 1)) +
        eLpNorm (fun x : ControlCarrier N => G2.groupConvolution G u (typeZeroUnitTail ν k) x)
          (ENNReal.ofReal p) (volume.restrict (ball 0 1)) := eLpNorm_add_le Fact.out
    _ ≤ C * eLpNorm u (ENNReal.ofReal p) volume + B * eLpNorm u (ENNReal.ofReal p) volume :=
      add_le_add hloc htail
    _ = _ := (add_mul C B _).symm

end RothschildStein.H3

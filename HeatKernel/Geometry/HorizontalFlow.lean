-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.AffineReparametrization
public import RothschildStein.Definitions.HomogeneousGroup.horizontalFields_contDiff
public import RothschildStein.G2.Measure
public import RothschildStein.G2.InvariantGlobalFlow
public import RothschildStein.G1.GeneralFlowUniqueness
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Complete horizontal flows and their control-metric displacement bounds. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped BigOperators Topology
namespace HeatKernel

/-- The tangent vector prescribed by constant horizontal controls. -/
def horizontalTangent {N q : ℕ} (hq : q ≤ N) (b : Fin q → ℝ) : Fin N → ℝ :=
  ∑ i, b i • Hormander.Interface.basisVec (Fin.castLE hq i)

/-- The left-invariant field with horizontal tangent is the controlled sum of horizontal fields. -/
theorem leftField_horizontalTangent {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (b : Fin q → ℝ) (x : Fin N → ℝ) :
    G2.leftField G (horizontalTangent hq b) x = ∑ i, b i • G.horizontalFields hq i x := by
  simp only [G2.leftField, horizontalTangent, map_sum, map_smul]
  rfl

/-- The global horizontal flow with constant control vector. -/
def horizontalFlow {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (b : Fin q → ℝ)
    (x : Fin N → ℝ) (t : ℝ) : Fin N → ℝ :=
  G.mul x (G2.leftExponential G (horizontalTangent hq b) t)

/-- The flow starts at its prescribed point. -/
@[simp] theorem horizontalFlow_zero {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (b : Fin q → ℝ) (x : Fin N → ℝ) : horizontalFlow G hq b x 0 = x := by
  simp only [horizontalFlow, G2.leftExponential_zero, G2.mul_zero]

/-- The horizontal flow solves the controlled equation at every real time. -/
theorem hasDerivAt_horizontalFlow {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (b : Fin q → ℝ) (x : Fin N → ℝ) (t : ℝ) :
    HasDerivAt (horizontalFlow G hq b x)
      (∑ i, b i • G.horizontalFields hq i (horizontalFlow G hq b x t)) t := by
  change HasDerivAt (fun u => G.mul x (G2.leftExponential G (horizontalTangent hq b) u))
    (∑ i, b i • G.horizontalFields hq i (G.mul x (G2.leftExponential G (horizontalTangent hq b) t))) t
  simpa only [leftField_horizontalTangent] using
    G2.leftExponential_translated_integralCurve G (horizontalTangent hq b) x t

/-- Horizontal flows are continuously differentiable in time. -/
theorem contDiff_one_horizontalFlow {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (b : Fin q → ℝ) (x : Fin N → ℝ) : ContDiff ℝ 1 (horizontalFlow G hq b x) := by
  have hd := hasDerivAt_horizontalFlow G hq b x
  have hc : Continuous (horizontalFlow G hq b x) :=
    continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (hd t).differentiableAt, ?_⟩
  have he : deriv (horizontalFlow G hq b x) =
      fun t => ∑ i, b i • G.horizontalFields hq i (horizontalFlow G hq b x t) :=
    funext fun t => (hd t).deriv
  rw [he]
  exact continuous_finsetSum _ (fun i _ =>
    ((G.horizontalFields_contDiff hq i).continuous.comp hc).const_smul (b i))

/-- Every finite time interval of a constant-control flow is a horizontal curve. -/
theorem isHorizontalCurveOn_horizontalFlow {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (b : Fin q → ℝ) (x : Fin N → ℝ) (s t : ℝ) :
    IsHorizontalCurveOn (G.horizontalFields hq) (horizontalFlow G hq b x) (fun i _ => b i) s t := by
  refine ⟨(contDiff_one_horizontalFlow G hq b x).contDiffOn.absolutelyContinuousOnInterval,
    fun _ => aemeasurable_const, ?_, Filter.Eventually.of_forall (hasDerivAt_horizontalFlow G hq b x)⟩
  change IntegrableOn (fun _ => Real.sqrt (∑ i, b i ^ 2)) (Icc s t)
  exact integrableOn_const measure_Icc_lt_top.ne

/-- Constant-control flow displacement is bounded by elapsed time times control norm. -/
theorem horizontalL2Distance_horizontalFlow_le {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (b : Fin q → ℝ) (x : Fin N → ℝ) (s t : ℝ) :
    horizontalL2Distance (G.horizontalFields hq) (horizontalFlow G hq b x s) (horizontalFlow G hq b x t) ≤
      ENNReal.ofReal (|t - s| * Real.sqrt (∑ i, b i ^ 2)) := by
  by_cases hst : s ≤ t
  · have hb := (isHorizontalCurveOn_horizontalFlow G hq b x s t).distance_le_controlLength hst
    simpa [controlNorm, sub_nonneg.mpr hst, abs_of_nonneg (sub_nonneg.mpr hst)] using hb
  · have hts := le_of_lt (lt_of_not_ge hst)
    have hb := (isHorizontalCurveOn_horizontalFlow G hq b x t s).distance_le_controlLength hts
    rw [horizontalL2Distance_comm] at hb
    simpa [controlNorm, sub_nonneg.mpr hts, abs_of_nonpos (sub_nonpos.mpr hts)] using hb

/-- Exponentials of left-invariant fields form one-parameter subgroups. -/
theorem leftExponential_add {N : ℕ} (G : HomogeneousGroup N) (v : Fin N → ℝ) (s t : ℝ) :
    G2.leftExponential G v (s + t) = G.mul (G2.leftExponential G v s) (G2.leftExponential G v t) := by
  let M := |t| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hα : ∀ u ∈ Ioo (-M) M,
      HasDerivAt (fun w => G2.leftExponential G v (s + w))
        (G2.leftField G v (G2.leftExponential G v (s + u))) u ∧
      G2.leftExponential G v (s + u) ∈ (univ : Set (Fin N → ℝ)) := by
    intro u _
    refine ⟨?_, mem_univ _⟩
    simpa only [Function.comp_def, one_smul] using
      (G2.leftExponential_integralCurve G v (s + u)).scomp u ((hasDerivAt_id u).const_add s)
  have he := G1.integralCurve_eqOn_general isOpen_univ (G2.contDiff_leftField G v).contDiffOn
    (show (0 : ℝ) ∈ Ioo (-M) M from ⟨by linarith, hM⟩) hα
    (fun u _ => ⟨G2.leftExponential_translated_integralCurve G v (G2.leftExponential G v s) u, mem_univ _⟩)
    (by simp only [add_zero, G2.leftExponential_zero, G2.mul_zero])
  apply he
  dsimp [M]
  constructor <;> linarith [le_abs_self t, neg_abs_le t]

/-- Horizontal flows compose by adding time. -/
theorem horizontalFlow_add {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (b : Fin q → ℝ) (x : Fin N → ℝ) (s t : ℝ) :
    horizontalFlow G hq b x (s + t) = horizontalFlow G hq b (horizontalFlow G hq b x s) t := by
  simp only [horizontalFlow, leftExponential_add, G2.mul_assoc]

/-- Every fixed-time horizontal flow preserves coordinate Lebesgue measure. -/
theorem measurePreserving_horizontalFlow {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (b : Fin q → ℝ) (t : ℝ) : MeasurePreserving (fun x => horizontalFlow G hq b x t) :=
  G2.measurePreserving_rightTranslation G (G2.leftExponential G (horizontalTangent hq b) t)

/-- Every fixed-time horizontal flow is a measurable embedding. -/
theorem measurableEmbedding_horizontalFlow {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (b : Fin q → ℝ) (t : ℝ) : MeasurableEmbedding (fun x => horizontalFlow G hq b x t) :=
  (measurePreserving_horizontalFlow G hq b t).measurable.measurableEmbedding
    (G2.rightTranslation_bijective G (G2.leftExponential G (horizontalTangent hq b) t)).injective

/-- Integral substitution by a fixed-time horizontal flow. -/
theorem integral_horizontalFlow {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (b : Fin q → ℝ) (t : ℝ) (f : (Fin N → ℝ) → ℝ) :
    ∫ x, f (horizontalFlow G hq b x t) = ∫ x, f x :=
  (measurePreserving_horizontalFlow G hq b t).integral_comp
    (measurableEmbedding_horizontalFlow G hq b t) f

end HeatKernel

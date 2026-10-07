-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.FlatParameterDerivative
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Normed.Operator.Bilinear

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Topology

namespace RothschildStein.G1

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The joint derivative formula retains h times the root derivative
as the regular quantity ρ(h) (BB Thm 1.48, pp. 32–34). -/
def flatParameterDerivative (H : P × E → E) (τ ρ : ℝ → P) (q : ℝ × E) :
    (ℝ × E) →L[ℝ] E :=
  ContinuousLinearMap.snd ℝ ℝ E +
    (ContinuousLinearMap.fst ℝ ℝ E).smulRight
      (H (τ q.1, q.2) + (fderiv ℝ H (τ q.1, q.2)) (ρ q.1, 0)) +
    (q.1 • fderiv ℝ H (τ q.1, q.2)).comp
      ((ContinuousLinearMap.inr ℝ P E).comp (ContinuousLinearMap.snd ℝ ℝ E))

/-- The derivative formula is jointly continuous, including h=0,
when the normalized root derivative ρ is continuous (BB pp. 32–34). -/
theorem flatParameterDerivative_continuous (H : P × E → E) (τ ρ : ℝ → P)
    (hH : ContDiff ℝ 1 H) (hτ : Continuous τ) (hρ : Continuous ρ) :
    Continuous (flatParameterDerivative H τ ρ) := by
  have harg : Continuous (fun q : ℝ × E => (τ q.1, q.2)) :=
    (hτ.comp continuous_fst).prodMk continuous_snd
  have hB : Continuous (fun q : ℝ × E => fderiv ℝ H (τ q.1, q.2)) :=
    (hH.continuous_fderiv (by norm_num)).comp harg
  have hcoef : Continuous (fun q : ℝ × E =>
      H (τ q.1, q.2) + (fderiv ℝ H (τ q.1, q.2)) (ρ q.1, 0)) :=
    (hH.continuous.comp harg).add
      (hB.clm_apply ((hρ.comp continuous_fst).prodMk continuous_const))
  have hrank : Continuous (fun q : ℝ × E =>
      (ContinuousLinearMap.fst ℝ ℝ E).smulRight
        (H (τ q.1, q.2) + (fderiv ℝ H (τ q.1, q.2)) (ρ q.1, 0))) := by
    change Continuous ((ContinuousLinearMap.smulRightL ℝ (ℝ × E) E
      (ContinuousLinearMap.fst ℝ ℝ E)) ∘ _)
    exact (ContinuousLinearMap.smulRightL ℝ (ℝ × E) E
      (ContinuousLinearMap.fst ℝ ℝ E)).continuous.comp hcoef
  exact (continuous_const.add hrank).add
    ((continuous_fst.smul hB).clm_comp continuous_const)

/-- Away from zero, the chain rule gives the regularized joint
formula; singular root derivatives occur only multiplied by h
(BB Thm 1.48, pp. 32–34). -/
theorem flatParameter_hasFDerivAt_of_root_derivative
    (H : P × E → E) (τ ρ : ℝ → P) (hH : ContDiff ℝ 1 H)
    (q : ℝ × E) (v : P) (hτ : HasDerivAt τ v q.1) (hρ : q.1 • v = ρ q.1) :
    HasFDerivAt (fun z : ℝ × E => z.2 + z.1 • H (τ z.1, z.2))
      (flatParameterDerivative H τ ρ q) q := by
  have harg : HasFDerivAt (fun z : ℝ × E => (τ z.1, z.2))
      (((ContinuousLinearMap.toSpanSingleton ℝ v).comp
        (ContinuousLinearMap.fst ℝ ℝ E)).prod (ContinuousLinearMap.snd ℝ ℝ E)) q := by
    simpa only [Function.comp_def] using
      (hτ.hasFDerivAt.comp q hasFDerivAt_fst).prodMk hasFDerivAt_snd
  have hh := (hH.differentiable (by norm_num) (τ q.1, q.2)).hasFDerivAt.comp q harg
  have hd := hasFDerivAt_snd.add (hasFDerivAt_fst.smul hh)
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro z
  simp only [flatParameterDerivative, Function.comp_def, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.inr_apply]
  have hsplit : (z.1 • v, z.2) = z.1 • (v, (0 : E)) + (0, z.2) := by
    ext <;> simp
  have hr : (fderiv ℝ H (τ q.1, q.2)) (ρ q.1, 0) =
      q.1 • (fderiv ℝ H (τ q.1, q.2)) (v, 0) := by
    rw [← hρ, ← map_smul]
    congr 1
    simp
  rw [hsplit, map_add, map_smul, hr, smul_add, smul_add, smul_smul, smul_smul]
  rw [mul_comm q.1 z.1]
  abel

/-- At zero the regularized derivative has identity spatial part
and the factor's initial coefficient as time part (BB pp. 32–34). -/
theorem flatParameterDerivative_zero (H : P × E → E) (τ ρ : ℝ → P)
    (hτ : τ 0 = 0) (hρ : ρ 0 = 0) (x : E) :
    flatParameterDerivative H τ ρ (0, x) =
      (ContinuousLinearMap.snd ℝ ℝ E) +
        (ContinuousLinearMap.toSpanSingleton ℝ (H (0, x))).comp
          (ContinuousLinearMap.fst ℝ ℝ E) := by
  simp only [flatParameterDerivative, hτ, hρ, ContinuousLinearMap.toSpanSingleton_comp,
    zero_smul, ContinuousLinearMap.zero_comp, add_zero]
  congr 1
  change (ContinuousLinearMap.fst ℝ ℝ E).smulRight
    (H (0, x) + (fderiv ℝ H (0, x)) (0 : P × E)) = _
  rw [map_zero, add_zero]

/-- A factored map is jointly C¹ when τ is continuous, smooth away
from zero, and hτ'(h) has a continuous extension vanishing at zero.
This includes the weighted absolute root powers (BB pp. 32–34). -/
theorem factoredParameter_contDiff_one
    (H : P × E → E) (τ ρ dτ : ℝ → P) (hH : ContDiff ℝ 1 H)
    (hτ : Continuous τ) (hρ : Continuous ρ) (hτ0 : τ 0 = 0) (hρ0 : ρ 0 = 0)
    (hdτ : ∀ h : ℝ, h ≠ 0 → HasDerivAt τ (dτ h) h)
    (hnorm : ∀ h : ℝ, h ≠ 0 → h • dτ h = ρ h) :
    ContDiff ℝ 1 (fun q : ℝ × E => q.2 + q.1 • H (τ q.1, q.2)) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨flatParameterDerivative H τ ρ,
    flatParameterDerivative_continuous H τ ρ hH hτ hρ, ?_⟩
  intro q
  rcases q with ⟨h, x⟩
  by_cases hz : h = 0
  · subst h
    have hc : ContinuousAt (fun q : ℝ × E => H (τ q.1, q.2)) (0, x) :=
      (hH.continuous.comp ((hτ.comp continuous_fst).prodMk continuous_snd)).continuousAt
    rw [flatParameterDerivative_zero H τ ρ hτ0 hρ0 x]
    simpa only [hτ0] using factoredParameter_hasFDerivAt_zero
      (fun q : ℝ × E => H (τ q.1, q.2)) x hc
  · exact flatParameter_hasFDerivAt_of_root_derivative H τ ρ hH (h, x) (dτ h)
      (hdτ h hz) (hnorm h hz)

end RothschildStein.G1

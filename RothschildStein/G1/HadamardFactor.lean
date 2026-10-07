-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.CompactParameterIntegral
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory

namespace RothschildStein.G1

universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [LocallyCompactSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The oriented FTC factor for the final scalar parameter. It is
well defined and smooth even when that parameter is zero
(BB Prop 1.50, pp. 28–29). -/
def hadamardFactor (G : E × ℝ → F) (q : E × ℝ) : F :=
  ∫ θ in Icc (0 : ℝ) 1, (fderiv ℝ G (q.1, θ * q.2)) (0, 1)

/-- Compact parameter averaging preserves smoothness of the FTC
factor through the vanishing-parameter hyperplane (BB Prop 1.50). -/
theorem hadamardFactor_contDiff (G : E × ℝ → F)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (hadamardFactor G) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun q : E × ℝ =>
    ∫ θ in Icc (0 : ℝ) 1, (fderiv ℝ G (q.1, θ * q.2)) (0, 1))
  apply compactParameterIntegral_contDiff
    (fun p : (E × ℝ) × ℝ => (fderiv ℝ G (p.1.1, p.2 * p.1.2)) (0, 1))
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ G) :=
    (contDiff_infty_iff_fderiv.mp hG).2
  have harg : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (E × ℝ) × ℝ => (p.1.1, p.2 * p.1.2)) :=
    contDiff_fst.fst.prodMk (contDiff_snd.mul contDiff_fst.snd)
  exact (hD.comp harg).clm_apply contDiff_const

omit [LocallyCompactSpace E] in
/-- Oriented FTC gives exact factorization for either sign of the
parameter, with no division by it (BB Prop 1.50, pp. 28–29). -/
theorem hadamardFactor_smul (G : E × ℝ → F)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (x : E) (t : ℝ) :
    t • hadamardFactor G (x, t) = G (x, t) - G (x, 0) := by
  have hs (v : ℝ) : HasDerivAt (fun w => G (x, w))
      ((fderiv ℝ G (x, v)) (0, 1)) v := by
    simpa only [Function.comp_def, ContinuousLinearMap.inr_apply] using
      ((hG.differentiable (by simp) (x, v)).hasFDerivAt).comp_hasDerivAt v
        ((hasDerivAt_const v x).prodMk (hasDerivAt_id v))
  have hcont : Continuous (fun θ : ℝ => (fderiv ℝ G (x, θ * t)) (0, 1)) :=
    ((hG.continuous_fderiv (by simp)).comp
      (continuous_const.prodMk (continuous_id.mul continuous_const))).clm_apply continuous_const
  have hh := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (f := fun w => G (x, w)) (f' := fun v => (fderiv ℝ G (x, v)) (0, 1))
    (z₀ := (0 : ℝ)) (z₁ := t)
    (by simpa only [zero_add, smul_eq_mul] using hcont.continuousOn)
    (fun θ _ => hs _)
  simpa only [hadamardFactor, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc, zero_add, smul_eq_mul] using hh

/-- A smooth function vanishing on the final parameter hyperplane
has a smooth exact factor, including at zero (BB Prop 1.50). -/
theorem exists_smooth_hadamardFactor (G : E × ℝ → F)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hzero : ∀ x, G (x, 0) = 0) :
    ∃ H : E × ℝ → F, ContDiff ℝ (⊤ : ℕ∞) H ∧
      ∀ x t, G (x, t) = t • H (x, t) := by
  refine ⟨hadamardFactor G, hadamardFactor_contDiff G hG, ?_⟩
  intro x t
  simpa only [hzero x, sub_zero] using (hadamardFactor_smul G hG x t).symm

omit [LocallyCompactSpace E] [CompleteSpace F] in
/-- Factoring one parameter preserves every other vanishing
hyperplane: an identically zero scalar slice has zero factor
(BB Prop 1.50, pp. 28–29). -/
theorem hadamardFactor_eq_zero_of_slice_zero (G : E × ℝ → F)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (x : E) (hz : ∀ t, G (x, t) = 0) (t : ℝ) :
    hadamardFactor G (x, t) = 0 := by
  have he (v : ℝ) : (fderiv ℝ G (x, v)) (0, 1) = 0 := by
    have hd : HasDerivAt (fun w => G (x, w))
        ((fderiv ℝ G (x, v)) (0, 1)) v := by
      simpa only [Function.comp_def] using ((hG.differentiable (by simp) (x, v)).hasFDerivAt).comp_hasDerivAt v
        ((hasDerivAt_const v x).prodMk (hasDerivAt_id v))
    have hzero : HasDerivAt (fun w => G (x, w)) 0 v := by
      simpa only [hz] using hasDerivAt_const v (0 : F)
    exact hd.unique hzero
  simp only [hadamardFactor, he, integral_zero]

end RothschildStein.G1

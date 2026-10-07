-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Asymptotics.Lemmas

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Asymptotics
open scoped Topology

namespace RothschildStein.G1

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Multiplication by the vanishing time parameter makes a continuous
coefficient jointly differentiable at time zero. Its coefficient need not
have a derivative there (BB Thm 1.48, pp. 32–34). -/
theorem flatParameter_hasFDerivAt_zero (H : ℝ × E → F) (x : E)
    (hH : ContinuousAt H (0, x)) :
    HasFDerivAt (fun q : ℝ × E => q.1 • H q)
      ((ContinuousLinearMap.toSpanSingleton ℝ (H (0, x))).comp
        (ContinuousLinearMap.fst ℝ ℝ E)) (0, x) := by
  rw [hasFDerivAt_iff_isLittleO]
  have hsmall : (fun q : ℝ × E => H q - H (0, x)) =o[𝓝 (0, x)]
      (fun _ => (1 : ℝ)) := by
    apply (isLittleO_one_iff ℝ).mpr
    simpa only [sub_self] using hH.tendsto.sub (tendsto_const_nhds (x := H (0, x)))
  have hbig : (fun q : ℝ × E => q.1) =O[𝓝 (0, x)]
      (fun q => ‖q - (0, x)‖) := by
    apply IsBigO.of_bound 1
    apply Eventually.of_forall
    intro q
    have h := norm_fst_le (q - (0, x))
    change ‖q.1 - 0‖ ≤ ‖q - (0, x)‖ at h
    simpa only [one_mul, norm_norm, sub_zero] using h
  have hh := hbig.smul_isLittleO hsmall
  have heq (q : ℝ × E) :
      q.1 • H q - (0 : ℝ) • H (0, x) -
        ((ContinuousLinearMap.toSpanSingleton ℝ (H (0, x))).comp
          (ContinuousLinearMap.fst ℝ ℝ E)) (q - (0, x)) =
        q.1 • (H q - H (0, x)) := by
    simp only [zero_smul, sub_zero, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_fst',
      Prod.fst_sub, smul_sub]
  simpa only [heq, smul_eq_mul, mul_one, isLittleO_norm_right] using hh

/-- Adding the initial point gives the joint zero-time derivative
of a factored quasiexponential (BB Thm 1.48, pp. 32–34). -/
theorem factoredParameter_hasFDerivAt_zero (H : ℝ × E → E) (x : E)
    (hH : ContinuousAt H (0, x)) :
    HasFDerivAt (fun q : ℝ × E => q.2 + q.1 • H q)
      ((ContinuousLinearMap.snd ℝ ℝ E) +
        (ContinuousLinearMap.toSpanSingleton ℝ (H (0, x))).comp
          (ContinuousLinearMap.fst ℝ ℝ E)) (0, x) :=
  hasFDerivAt_snd.add (flatParameter_hasFDerivAt_zero H x hH)

end RothschildStein.G1

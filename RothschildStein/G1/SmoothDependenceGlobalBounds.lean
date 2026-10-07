-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceGlobalLinear
public import RothschildStein.G1.VariationBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter Function ODE
open scoped Topology NNReal

namespace RothschildStein.G1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Obtain ambient time derivatives even at the endpoints of
a prescribed bounded interval, by constant extension of the coefficient and
solution on a larger interval (BB Proposition 1.2, p. 3). -/
theorem exists_linear_integralCurve_hasDerivAt_on_Icc
    {T : ℝ} (hT : 0 ≤ T) (A : ℝ → E →L[ℝ] E)
    (hc : ContinuousOn A (Icc (-T) T)) {K : ℝ≥0}
    (hb : ∀ t ∈ Icc (-T) T, ‖A t‖ ≤ K) (w₀ : E) :
    ∃ W : ℝ → E, Continuous W ∧ W 0 = w₀ ∧
      ∀ t ∈ Icc (-T) T, HasDerivAt W (A t (W t)) t := by
  let B : ℝ → E →L[ℝ] E := fun t => A (projIcc (-T) T (by linarith) t)
  have hcB : Continuous B :=
    (continuousOn_iff_continuous_domRestrict.mp hc).comp continuous_projIcc
  have hbB : ∀ t ∈ Icc (-(T + 1)) (T + 1), ‖B t‖ ≤ K :=
    fun t _ => hb _ (projIcc (-T) T (by linarith) t).property
  obtain ⟨W, hcW, hW0, hWd⟩ := exists_linear_integralCurve_on_Icc
    (show 0 ≤ T + 1 by linarith) B hcB.continuousOn hbB w₀
  refine ⟨W, hcW, hW0, fun t ht => ?_⟩
  have hti : t ∈ Ioo (-(T + 1)) (T + 1) := by constructor <;> linarith [ht.1, ht.2]
  have hd := (hWd t (Ioo_subset_Icc_self hti)).hasDerivAt (Icc_mem_nhds hti.1 hti.2)
  simpa only [B, projIcc_of_mem _ ht] using hd

omit [CompleteSpace E] in
/-- A linear solution has a uniform bound on an arbitrary
bounded interval. The bound depends only on its initial norm and the
coefficient norm bound (BB Proposition 1.2, p. 3). -/
theorem linear_integralCurve_norm_bound
    {T : ℝ} (hT : 0 ≤ T) {A : ℝ → E →L[ℝ] E} {K : ℝ≥0} {W : ℝ → E}
    (hb : ∀ t ∈ Icc (-T) T, ‖A t‖ ≤ K)
    (hWd : ∀ t ∈ Icc (-T) T, HasDerivAt W (A t (W t)) t) :
    ∀ t ∈ Icc (-T) T, ‖W t‖ ≤ ‖W 0‖ * Real.exp ((K : ℝ) * T) := by
  intro t ht
  have hs : uIcc (0 : ℝ) t ⊆ Icc (-T) T :=
    uIcc_subset_Icc ⟨by linarith, hT⟩ ht
  have he := norm_le_exp_of_deriv_bound_uIcc
    (fun v hv => hWd v (hs hv))
    (fun v hv => ((A v).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hb v (hs hv)) (norm_nonneg _))) (le_refl ‖W 0‖)
  apply he.trans
  have habs : |t| ≤ T := abs_le.mpr ht
  gcongr

end RothschildStein.G1

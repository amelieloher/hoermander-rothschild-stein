-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace RothschildStein.G1

universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [LocallyCompactSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Differentiation of a compact parameter integral uses a bound
obtained on a compact neighborhood, rather than a global derivative bound
(BB Prop 1.50, pp. 28–29). -/
theorem compactParameterIntegral_hasFDerivAt
    (G : E × ℝ → F) (D : E × ℝ → E →L[ℝ] F)
    (hG : Continuous G) (hD : Continuous D)
    (hd : ∀ x t, HasFDerivAt (fun y => G (y, t)) (D (x, t)) x)
    (x : E) :
    HasFDerivAt (fun y => ∫ t in Icc (0 : ℝ) 1, G (y, t))
      (∫ t in Icc (0 : ℝ) 1, D (x, t)) x := by
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  obtain ⟨M, hM⟩ := (hK.prod isCompact_Icc).bddAbove_image hD.norm.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := K)
    (bound := fun _ => M) hKx
  · filter_upwards with y
    exact (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hG.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
      isCompact_Icc
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht y hy
    exact hM (mem_image_of_mem _ ⟨hy, ht⟩)
  · exact integrableOn_const isCompact_Icc.measure_ne_top
  · exact Eventually.of_forall (fun t y _ => hd y t)

/-- Integration over a fixed compact interval preserves every finite
order of joint smoothness (BB Prop 1.50, pp. 28–29). -/
theorem compactParameterIntegral_contDiff_nat (n : ℕ) (G : E × ℝ → F)
    (hG : ContDiff ℝ n G) :
    ContDiff ℝ n (fun x => ∫ t in Icc (0 : ℝ) 1, G (x, t)) := by
  induction n generalizing F with
  | zero =>
    change ContDiff ℝ 0 _
    rw [contDiff_zero]
    exact continuous_parametric_integral_of_continuous
      (f := fun x t => G (x, t)) hG.continuous isCompact_Icc
  | succ n ih =>
    let D : E × ℝ → E →L[ℝ] F := fun q =>
      (fderiv ℝ G q).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hDG : ContDiff ℝ n (fderiv ℝ G) :=
      (contDiff_succ_iff_fderiv.mp hG).2.2
    have hD : ContDiff ℝ n D := hDG.clm_comp contDiff_const
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun x => ∫ t in Icc (0 : ℝ) 1, D (x, t), ih D hD, ?_⟩
    intro x
    apply compactParameterIntegral_hasFDerivAt G D hG.continuous hD.continuous
    intro y t
    exact ((hG.differentiable (by simp) (y, t)).hasFDerivAt).comp y
      (by simpa only [ContinuousLinearMap.inl_apply, Prod.mk_add_mk, zero_add, add_zero]
        using (ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt.const_add (0, t))

/-- A smooth compact parameter integral is smooth at all orders
(BB Prop 1.50, pp. 28–29). -/
theorem compactParameterIntegral_contDiff (G : E × ℝ → F)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ t in Icc (0 : ℝ) 1, G (x, t)) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro n _
  exact compactParameterIntegral_contDiff_nat n G (hG.of_le (by simp))

end RothschildStein.G1

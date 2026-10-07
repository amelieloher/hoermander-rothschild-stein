-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.CompactParameterIntegral

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1

universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [LocallyCompactSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {N : ℕ}

omit [CompleteSpace F] in
/-- Differentiation under a fixed compact kernel
integral follows from a derivative bound on a compact parameter
neighborhood. The integration coordinates may have a different dimension. -/
theorem compactKernelIntegral_hasFDerivAt
    (Φ : E × (Fin N → ℝ) → F) (D : E × (Fin N → ℝ) → E →L[ℝ] F)
    (hΦ : Continuous Φ) (hD : Continuous D)
    (hd : ∀ x a, HasFDerivAt (fun y => Φ (y, a)) (D (x, a)) x)
    (K : Set (Fin N → ℝ)) (hK : IsCompact K) (x : E) :
    HasFDerivAt (fun y => ∫ a in K, Φ (y, a)) (∫ a in K, D (x, a)) x := by
  obtain ⟨L, hL, hx⟩ := exists_compact_mem_nhds x
  obtain ⟨M, hM⟩ := (hL.prod hK).bddAbove_image hD.norm.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := L) (bound := fun _ => M) hx
  · filter_upwards with y
    exact (hΦ.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hΦ.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hK
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha y hy
    exact hM (mem_image_of_mem _ ⟨hy, ha⟩)
  · exact integrableOn_const hK.measure_ne_top
  · exact Filter.Eventually.of_forall (fun a y _ => hd y a)

/-- A jointly C^m compact kernel integral is C^m
in its parameters, including all orders needed for a smooth flux multiplier. -/
theorem compactKernelIntegral_contDiff_nat (m : ℕ) (Φ : E × (Fin N → ℝ) → F)
    (hΦ : ContDiff ℝ m Φ) (K : Set (Fin N → ℝ)) (hK : IsCompact K) :
    ContDiff ℝ m (fun x => ∫ a in K, Φ (x, a)) := by
  induction m generalizing F with
  | zero =>
    change ContDiff ℝ 0 _
    rw [contDiff_zero]
    exact continuous_parametric_integral_of_continuous (f := fun x a => Φ (x, a)) hΦ.continuous hK
  | succ m ih =>
    let D : E × (Fin N → ℝ) → E →L[ℝ] F := fun q =>
      (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E (Fin N → ℝ))
    have hD : ContDiff ℝ m D := (contDiff_succ_iff_fderiv.mp hΦ).2.2.clm_comp contDiff_const
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun x => ∫ a in K, D (x, a), ih D hD, ?_⟩
    intro x
    apply compactKernelIntegral_hasFDerivAt Φ D hΦ.continuous hD.continuous ?_ K hK x
    intro y a
    exact ((hΦ.differentiable (by simp) (y, a)).hasFDerivAt).comp y
      (by simpa only [ContinuousLinearMap.inl_apply, Prod.mk_add_mk, zero_add, add_zero]
        using (ContinuousLinearMap.inl ℝ E (Fin N → ℝ)).hasFDerivAt.const_add (0, a))

/-- Integration over a fixed compact model annulus
preserves full joint smoothness in the endpoint parameters. -/
theorem compactKernelIntegral_contDiff (Φ : E × (Fin N → ℝ) → F)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (K : Set (Fin N → ℝ)) (hK : IsCompact K) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ a in K, Φ (x, a)) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro m hm
  exact compactKernelIntegral_contDiff_nat m Φ (hΦ.of_le (by simp)) K hK

end RothschildStein.P1

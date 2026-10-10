-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.GeneratorErrorOperators

/-! # Identification of the heat generator on the resolvent range

The strong right difference quotient is computed directly from continuous functional
calculus and the dense-range error estimate.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace HeatKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem generatorErrorOperator_eq (R : E →L[ℂ] E) (hR : IsSelfAdjoint R) (t : ℝ) :
    generatorErrorOperator R t =
      t⁻¹ • ((cfc (heatMultiplier t) R - 1) * R) - (R - 1) := by
  have hc : ContinuousOn (fun r => heatMultiplier t r - 1) (spectrum ℝ R) :=
    ((continuous_heatMultiplier t).sub continuous_const).continuousOn
  have hi : ContinuousOn (fun r : ℝ => r - 1) (spectrum ℝ R) :=
    (continuous_id.sub continuous_const).continuousOn
  have hm : ContinuousOn (fun r => (heatMultiplier t r - 1) * r) (spectrum ℝ R) :=
    hc.mul continuous_id.continuousOn
  have hsm : ContinuousOn (fun r => t⁻¹ • ((heatMultiplier t r - 1) * r))
      (spectrum ℝ R) := hm.const_smul t⁻¹
  have hfn : generatorMultiplierError t =
      (fun r : ℝ => t⁻¹ • ((heatMultiplier t r - 1) * r) - (r - 1)) := by
    ext r
    simp only [generatorMultiplierError, smul_eq_mul, div_eq_mul_inv]
    ring
  unfold generatorErrorOperator
  rw [hfn, cfc_sub (fun r => t⁻¹ • ((heatMultiplier t r - 1) * r)) (fun r : ℝ => r - 1) R hsm hi,
    cfc_smul t⁻¹ (fun r => (heatMultiplier t r - 1) * r) R hm,
    cfc_mul (fun r => heatMultiplier t r - 1) (fun r : ℝ => r) R hc continuous_id.continuousOn,
    cfc_sub (heatMultiplier t) (fun _ => 1) R
      (continuous_heatMultiplier t).continuousOn continuous_const.continuousOn,
    cfc_sub (fun r : ℝ => r) (fun _ => 1) R
      continuous_id.continuousOn continuous_const.continuousOn,
    cfc_id' ℝ R hR, cfc_const_one ℝ R hR]

theorem generatorErrorOperator_apply_eq (R : E →L[ℂ] E) (hR : IsSelfAdjoint R)
    (t : ℝ) (x : E) :
    generatorErrorOperator R t x =
      t⁻¹ • ((cfc (heatMultiplier t) R : E →L[ℂ] E) (R x) - R x) - (R x - x) := by
  rw [generatorErrorOperator_eq R hR]
  simp only [sub_apply, smul_apply, mul_apply_eq_comp, one_apply_eq_self]

theorem tendsto_heat_cfc_differenceQuotient_range (R : E →L[ℂ] E)
    (hR : IsSelfAdjoint R) (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (hdense : DenseRange R) (x : E) :
    Tendsto (fun t : ℝ => t⁻¹ •
      ((cfc (heatMultiplier t) R : E →L[ℂ] E) (R x) - R x))
      (𝓝[>] 0) (𝓝 (R x - x)) := by
  have h := (tendsto_generatorErrorOperator_apply_of_denseRange R hR hspec hdense x).add_const (R x - x)
  simp only [zero_add] at h
  convert h using 1
  ext t
  rw [generatorErrorOperator_apply_eq R hR t x]
  abel


theorem heat_cfc_commute_apply (R : E →L[ℂ] E) (hR : IsSelfAdjoint R)
    (t : ℝ) (x : E) :
    R ((cfc (heatMultiplier t) R : E →L[ℂ] E) x) =
      (cfc (heatMultiplier t) R : E →L[ℂ] E) (R x) := by
  have hc : Commute R (cfc (heatMultiplier t) R) := by
    simpa only [cfc_id' ℝ R hR] using
      cfc_commute_cfc (fun r : ℝ => r) (heatMultiplier t) R
  simpa only [mul_apply_eq_comp] using congrArg (fun T : E →L[ℂ] E => T x) hc.eq

theorem tendsto_heat_cfc_differenceQuotient_iff (R : E →L[ℂ] E)
    (hR : IsSelfAdjoint R) (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (hdense : DenseRange R) (u g : E) :
    Tendsto (fun t : ℝ => t⁻¹ • ((cfc (heatMultiplier t) R : E →L[ℂ] E) u - u))
      (𝓝[>] 0) (𝓝 (-g)) ↔ R (u + g) = u := by
  constructor
  · intro h
    have hlim := (R.continuous.tendsto (-g)).comp h
    have hrange := tendsto_heat_cfc_differenceQuotient_range R hR hspec hdense u
    have hfun (t : ℝ) : R (t⁻¹ • ((cfc (heatMultiplier t) R : E →L[ℂ] E) u - u)) =
        t⁻¹ • ((cfc (heatMultiplier t) R : E →L[ℂ] E) (R u) - R u) := by
      rw [R.map_smul_of_tower, map_sub, heat_cfc_commute_apply R hR t u]
    have he : R (-g) = R u - u := tendsto_nhds_unique (hlim.congr hfun) hrange
    rw [map_neg] at he
    rw [map_add]
    have he' := congrArg Neg.neg he
    simp only [neg_neg, neg_sub] at he'
    rw [he']
    abel
  · intro h
    have hrange := tendsto_heat_cfc_differenceQuotient_range R hR hspec hdense (u + g)
    simpa only [h, sub_add_cancel_left] using hrange

end HeatKernel

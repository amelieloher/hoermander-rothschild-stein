-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderRegularization
public import RothschildStein.H3.SphereMaximum
public import RothschildStein.H3.TypeZero
public import RothschildStein.G2.PowerBochner
public import RothschildStein.G2.MollifierUniform
public import RothschildStein.G2.MollifierSmooth
public import RothschildStein.H1.PrincipalValueDefs
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace RothschildStein.H3

/-- The subtracted near principal-value integral of actual
mollifiers converges pointwise. A fixed positive Hölder exponent supplies
the integrable power α−Q; no singular-integral norm estimate is assumed.
BB Proposition 8.49, p. 379. -/
theorem tendsto_principalValueNear_groupRegularize {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (hsym : ν.Symmetric) (φ : G2.GroupMollifier G ν)
    {K f : (Fin N → ℝ) → ℝ} (hK : TypeZero G ν K)
    (hf : Continuous f) (hc : HasCompactSupport f) {α H : ℝ} (hα : 0 < α)
    (hholder : ∀ x y, |f x - f y| ≤ H * G2.gaugeDistance G ν x y ^ α)
    (x : Fin N → ℝ) :
    Tendsto (fun ε : ℝ => H1.principalValueNear G ν K (G2.groupRegularize G φ f ε) x)
      (𝓝[>] 0) (𝓝 (H1.principalValueNear G ν K f x)) := by
  let nonemptyFin : Nonempty (Fin N) := ⟨⟨0, G.dimension_pos⟩⟩
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hc
  let Λ := kernelSphereBound ν K
  have hΛ : 0 ≤ Λ := (kernelSphereBound_continuous ν.gauge hK.smooth.continuousOn).1
  have hkb := kernelSphereBound_homogeneous ν.gauge hK.smooth.continuousOn hK.homogeneous
  have hki : AEStronglyMeasurable K volume :=
    hK.smooth.continuousOn.stronglyMeasurable_of_countable_compl (by simp) |>.aestronglyMeasurable
  have hp : IntegrableOn (fun w => (ν w) ^ (α - (G.homogeneousDimension : ℝ))) {w | ν w < 1} volume := by
    have hh := (G2.integrableOn_power_near_iff ν.gauge
      ((G.homogeneousDimension : ℝ) - α) zero_lt_one).mpr (by linarith)
    have he : -((G.homogeneousDimension : ℝ) - α) = α - (G.homogeneousDimension : ℝ) := by ring
    rw [he] at hh
    exact hh.mono_set (by
      intro w hw
      change ν w ≤ 1
      exact le_of_lt hw)
  have hm : ∀ᶠ ε : ℝ in 𝓝[>] 0, AEStronglyMeasurable
      (fun w => K w * (G2.groupRegularize G φ f ε (G.mul x (G.inv w)) -
        G2.groupRegularize G φ f ε x)) (volume.restrict {w | ν w < 1}) := by
    filter_upwards [self_mem_nhdsWithin] with ε he
    have hreg := (G2.contDiff_groupRegularize G φ he (p := (1 : ℝ≥0∞)) le_rfl
      (hf.memLp_of_hasCompactSupport hc)).continuous
    have hcomp : Continuous (fun w => G2.groupRegularize G φ f ε (G.mul x (G.inv w))) := hreg.comp ((G2.continuous_mul G).comp (continuous_const.prodMk (G2.continuous_inv G)))
    exact (hki.mul (hcomp.sub continuous_const).aestronglyMeasurable).mono_measure Measure.restrict_le_self
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ w ∂volume.restrict {w | ν w < 1},
      ‖K w * (G2.groupRegularize G φ f ε (G.mul x (G.inv w)) -
        G2.groupRegularize G φ f ε x)‖ ≤
        (Λ * H) * (ν w) ^ (α - (G.homogeneousDimension : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with ε he
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : Fin N → ℝ))] with w hw
    have hd : G2.gaugeDistance G ν (G.mul x (G.inv w)) x = ν w := by
      change ν (G.mul (G.inv x) (G.mul x (G.inv w))) = ν w
      rw [← G2.mul_assoc, G2.inv_mul, G2.zero_mul, hsym]
    have hh := groupRegularize_holder_bound G ν φ hf hM hholder he (G.mul x (G.inv w)) x
    rw [hd] at hh
    have hn : 0 < ν w := lt_of_le_of_ne (ν.gauge.2.1 w)
      (Ne.symm fun hz => hw ((ν.gauge.2.2.1 w).mp hz))
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      _ ≤ (Λ * (ν w) ^ (-(G.homogeneousDimension : ℝ))) * (H * (ν w) ^ α) :=
        mul_le_mul (hkb w hw) hh (abs_nonneg _) (by positivity)
      _ = _ := by
        rw [show α - (G.homogeneousDimension : ℝ) = -(G.homogeneousDimension : ℝ) + α by ring,
          Real.rpow_add hn]
        ring
  have hpoint := G2.tendstoUniformly_groupRegularize G φ hf hc
  exact tendsto_integral_filter_of_dominated_convergence
    (fun w => (Λ * H) * (ν w) ^ (α - (G.homogeneousDimension : ℝ))) hm hb
    (hp.const_mul (Λ * H)) (Eventually.of_forall fun w =>
      ((hpoint.tendsto_at (G.mul x (G.inv w))).sub (hpoint.tendsto_at x)).const_mul (K w))

end RothschildStein.H3

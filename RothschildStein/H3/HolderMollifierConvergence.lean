-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderRegularizationNorm
public import RothschildStein.H3.HolderInterpolationExplicit
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import RothschildStein.H3.HolderUniformSup
public import RothschildStein.G2.MollifierUniform

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped ENNReal NNReal Topology
namespace RothschildStein.H3
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Actual group mollifiers converge to the compact input in
 every strictly lower Hölder exponent (BB Theorem 8.52, pp. 381–382). -/
theorem tendsto_holderNorm_groupRegularize_sub
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (φ : G2.GroupMollifier G ν) {a b : ℝ≥0} (ha : 0 < a) (hba : b < a)
    {f : ControlCarrier N → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    letI metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
    @H2.BoundedHolder (ControlCarrier N) metric a univ f →
    Tendsto (fun ε : ℝ => @H2.boundedHolderNorm (ControlCarrier N) metric b univ
      (fun x => G2.groupRegularize G φ f ε x - f x)) (𝓝[>] 0) (𝓝 0) := by
  let metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
  intro hb
  let F : ℝ → ControlCarrier N → ℝ := fun ε x => G2.groupRegularize G φ f ε x - f x
  let S : ℝ → ℝ≥0∞ := fun ε => H2.holderSup univ (F ε)
  let H : ℝ := (@H2.holderSemi (ControlCarrier N) metric a univ f).toReal
  have hM (x : Fin N → ℝ) : ‖f x‖ ≤ (H2.holderSup univ f).toReal :=
    H2.abs_le_holderSup hb.parts.1 (mem_univ x)
  have hH (x y : Fin N → ℝ) : |f x - f y| ≤ H * G2.gaugeDistance G ν x y ^ (a : ℝ) :=
    H2.sub_le_holderSemi hb.parts.2 (mem_univ (x : ControlCarrier N))
      (mem_univ (y : ControlCarrier N))
  have hsup : Tendsto S (𝓝[>] 0) (𝓝 0) :=
    tendsto_holderSup_sub_zero_of_uniform _ _ _ (G2.tendstoUniformly_groupRegularize G φ hf hc)
  have hlim : Tendsto (fun ε => (S ε).toReal) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsup
  have hbound (ε : ℝ) (he : 0 < ε) : S ε < ⊤ := by
    apply (H2.holderSup_le_of_bound (A := (univ : Set (ControlCarrier N))) (M :=
      2 * (H2.holderSup univ f).toReal) ?_).trans_lt ENNReal.ofReal_lt_top
    intro x _
    have hr := G2.norm_groupRegularize_le G φ hf hM he x
    have hx := hM x
    have ht := abs_sub (G2.groupRegularize G φ f ε x) (f x)
    dsimp [F]
    simpa only [Real.norm_eq_abs] using ht.trans (by simpa only [Real.norm_eq_abs, two_mul] using add_le_add hr hx)
  have hdiff (ε : ℝ) (he : 0 < ε) (x y : ControlCarrier N) :
      |F ε x - F ε y| ≤ (2 * H) * @dist (ControlCarrier N) metric.toDist x y ^ (a : ℝ) := by
    have hr := groupRegularize_holder_bound G ν φ hf hM hH he x y
    have hx := hH x y
    have ht := abs_sub (G2.groupRegularize G φ f ε x - G2.groupRegularize G φ f ε y) (f x - f y)
    have hid : F ε x - F ε y =
        (G2.groupRegularize G φ f ε x - G2.groupRegularize G φ f ε y) - (f x - f y) := by
      dsimp [F]; ring
    rw [hid]
    change _ ≤ (2 * H) * G2.gaugeDistance G ν x y ^ (a : ℝ)
    linarith
  have hup : Tendsto (fun ε => ENNReal.ofReal (S ε).toReal +
      ENNReal.ofReal ((2 * (S ε).toReal) ^ (1 - (b : ℝ) / (a : ℝ)) *
        (2 * H) ^ ((b : ℝ) / (a : ℝ)))) (𝓝[>] 0) (𝓝 0) := by
    have hexp : 0 < 1 - (b : ℝ) / (a : ℝ) :=
      sub_pos.mpr ((div_lt_one (show 0 < (a : ℝ) from ha)).mpr hba)
    have hp := (Real.continuousAt_rpow_const 0 _ (Or.inr hexp.le)).tendsto.comp
      (show Tendsto (fun ε => 2 * (S ε).toReal) (𝓝[>] 0) (𝓝 (0 : ℝ)) by
        simpa only [mul_zero] using hlim.const_mul 2)
    simpa only [Function.comp_def, Real.zero_rpow hexp.ne', zero_mul,
      ENNReal.ofReal_zero, zero_add] using
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim).add
        (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hp.mul_const ((2 * H) ^ ((b : ℝ) / (a : ℝ)))))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [self_mem_nhdsWithin] with ε he
  exact boundedHolderNorm_le_interpolation_bound ha hba.le univ ENNReal.toReal_nonneg
    (by dsimp [H]; positivity)
    (fun x hx => H2.abs_le_holderSup (hbound ε he) hx)
    (fun x _ y _ => hdiff ε he x y)

end RothschildStein.H3

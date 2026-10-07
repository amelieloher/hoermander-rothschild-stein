-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroRadiusHolderSmooth
public import RothschildStein.H3.GroupMollification
public import RothschildStein.H3.MollifierPrincipalValueLimit
public import RothschildStein.H3.HolderLowerSemicontinuity
public import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace RothschildStein.H3

/-- Universal Hölder estimate for the full actual type-zero
PV convolution on any fixed positive-radius ball. Compact continuous Hölder inputs are
approximated by the actual group mollifier; every certificate is constructed. -/
theorem exists_typeZero_radius_holder_bound_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N)
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (C : G2.ControlNormConclusion G driftWeight Y)
    (hY : ∀ i, ContinuousOn (Y i) {0}ᶜ)
    (hhomY : ∀ i, G2.IsHomogeneousField G (Y i) (if i = 0 then 2 else 1))
    {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1) {R : ℝ} (hR : 0 < R) :
    let _metric := gaugeMetric G C.norm C.constant_one C.symmetric
    let E := ball (0 : ControlCarrier N) R
    ∃ B : ℝ, 0 < B ∧ ∀ (k : (Fin N → ℝ) → ℝ), TypeZero G C.norm k →
      ∀ (F : ControlCarrier N → ℝ), Continuous F →
      HasCompactSupport F → tsupport F ⊆ E → H2.BoundedHolder a E F →
      H2.boundedHolderNorm a E (fun x : ControlCarrier N =>
        H1.principalValueConvolution G C.norm k (fun y : Fin N → ℝ => F y) x) ≤
        ENNReal.ofReal (kernelDerivativeBound C.norm k 1 * B) * H2.boundedHolderNorm a E F := by
  classical
  let _metric := gaugeMetric G C.norm C.constant_one C.symmetric
  let E := ball (0 : ControlCarrier N) R
  obtain ⟨B, hB, hbound⟩ := exists_typeZero_radius_holder_bound_smooth_of_controlNorm G C hY hhomY ha ha1 hR
  obtain ⟨φ⟩ := G2.nonempty_groupMollifier G C.norm
  dsimp only
  refine ⟨B, hB, ?_⟩
  intro k hk F hF hc hs hf
  let F₀ : (Fin N → ℝ) → ℝ := fun x => F x
  have hball : E = {y : ControlCarrier N | C.norm y < R} := by
    ext y
    change C.norm (G.mul (G.inv 0) y) < R ↔ C.norm y < R
    rw [G2.inv_zero, G2.zero_mul]
  have hs₀ : tsupport F₀ ⊆ {x : Fin N → ℝ | C.norm x < R} := by
    intro x hx
    have hh := hs hx
    change x ∈ E at hh
    rw [hball] at hh
    exact hh
  have hext : H2.boundedHolderNorm a univ F = H2.boundedHolderNorm a E F :=
    boundedHolderNorm_global_eq_of_controlNorm C isOpen_ball hc hs
  have hfg : @H2.BoundedHolder (ControlCarrier N) _metric a univ F₀ := by
    change H2.boundedHolderNorm a univ F < ⊤
    rw [hext]
    exact hf
  obtain ⟨hreg, _, hcontr, _⟩ := group_mollification G C.norm C.constant_one C.symmetric
    φ ha (show Continuous F₀ from hF) hc hs₀ hfg
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hpos (j : ℕ) : 0 < ε j := by dsimp only [ε]; positivity
  have ht : Tendsto ε atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall hpos⟩
  let Fn : ℕ → ControlCarrier N → ℝ := fun j x => G2.groupRegularize G φ F₀ (ε j) x
  have hFn (j : ℕ) : H2.boundedHolderNorm a E (Fn j) ≤ H2.boundedHolderNorm a E F :=
    (H2.boundedHolderNorm_restrict (subset_univ _)).trans
      ((hcontr (ε j) (hpos j)).2.2.trans_eq hext)
  have hregn := ht.eventually hreg
  have hb : ∀ᶠ j in atTop,
      H2.boundedHolderNorm a E (fun x : ControlCarrier N =>
        H1.principalValueConvolution G C.norm k (fun y : Fin N → ℝ => Fn j y) x) ≤
      ENNReal.ofReal (kernelDerivativeBound C.norm k 1 * B) * H2.boundedHolderNorm a E F := by
    filter_upwards [hregn] with j hj
    have hsFn : tsupport (Fn j) ⊆ E := by
      rw [hball]
      exact hj.2.2
    exact (hbound k hk (Fn j) (hj.1.of_le (by simp)) hj.2.1 hsFn
      ((hFn j).trans_lt hf)).trans (mul_le_mul' le_rfl (hFn j))
  have hholder : ∀ x y : Fin N → ℝ, |F₀ x - F₀ y| ≤
      (H2.holderSemi a univ F).toReal * G2.gaugeDistance G C.norm x y ^ (a : ℝ) := by
    intro x y
    exact @H2.sub_le_holderSemi (ControlCarrier N) _metric a univ F hfg.parts.2 x y
      (mem_univ _) (mem_univ _)
  have hpoint : ∀ x ∈ E, Tendsto
      (fun j => H1.principalValueConvolution G C.norm k (fun y : Fin N → ℝ => Fn j y) x)
      atTop (𝓝 (H1.principalValueConvolution G C.norm k F₀ x)) := by
    intro x _
    exact (tendsto_principalValueConvolution_groupRegularize G C.norm C.symmetric φ hk
      (show Continuous F₀ from hF) hc (show 0 < (a : ℝ) from ha) hholder x).comp ht
  have hlimit := boundedHolderNorm_le_liminf (X := ControlCarrier N) (a := a) (A := E) hpoint
  exact hlimit.trans (liminf_le_of_frequently_le' hb.frequently)

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroRadiusHolder
public import RothschildStein.H3.FundamentalControlNorm
public import RothschildStein.H3.FundamentalSecondTypeZero

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric TopologicalSpace
open scoped NNReal ENNReal
namespace RothschildStein.H3

/-- Construct the exact bounded-domain PV Hölder callback for
all actual second fundamental kernels. No analytic PV bound is assumed. -/
theorem exists_fundamental_second_PV_holder_bounds_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H)
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1) (V : Opens (Fin N → ℝ))
    {R : ℝ} (hR : 0 < R) (hVR : ∀ x ∈ V, C.norm x < R) :
    let _metric : MetricSpace (ControlCarrier N) := gaugeMetric G C.norm C.constant_one C.symmetric
    ∃ B : Fin q → Fin q → ℝ, (∀ i j, 0 ≤ B i j) ∧
      ∀ F : ControlCarrier N → ℝ, Continuous F → HasCompactSupport F →
      tsupport F ⊆ (V : Set (Fin N → ℝ)) → H2.BoundedHolder a univ F → ∀ i j,
      @H2.boundedHolderNorm (ControlCarrier N) _metric a (V : Set (Fin N → ℝ))
        (fun x => H1.principalValueConvolution G C.norm
          (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K))
          (fun y : Fin N → ℝ => F y) x) ≤
        ENNReal.ofReal (B i j) *
          @H2.boundedHolderNorm (ControlCarrier N) _metric a (V : Set (Fin N → ℝ)) F := by
  let _metric : MetricSpace (ControlCarrier N) := gaugeMetric G C.norm C.constant_one C.symmetric
  let V₀ : Opens (ControlCarrier N) := ⟨(V : Set (Fin N → ℝ)), V.isOpen⟩
  let E := ball (0 : ControlCarrier N) R
  have hVE : (V₀ : Set (ControlCarrier N)) ⊆ E := by
    intro x hx
    change C.norm (G.mul (G.inv 0) x) < R
    rw [G2.inv_zero, G2.zero_mul]
    exact hVR x hx
  obtain ⟨B₀, hB₀, hb⟩ := exists_typeZero_radius_holder_bound_of_controlNorm G C
    (fun i => (H.fields_smooth G i).continuous.continuousOn) H.homogeneous ha ha1 hR
  have hk (i j : Fin q) : TypeZero G C.norm
      (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) :=
    fundamental_second_typeZero G (standingWithNorm G H C.norm)
      (fundamentalKernelWithNorm G H C.norm K) i j
  let B := fun i j : Fin q => kernelDerivativeBound C.norm
    (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) 1 * B₀
  dsimp only
  refine ⟨B, ?_, ?_⟩
  · intro i j
    exact mul_nonneg (kernelDerivativeBound_properties C.norm.gauge (hk i j).smooth 1).1 hB₀.le
  · intro F hF hc hs hf i j
    have hsV : tsupport F ⊆ (V₀ : Set (ControlCarrier N)) := hs
    have hsE : tsupport F ⊆ E := hsV.trans hVE
    have hfE : H2.BoundedHolder a E F :=
      (H2.boundedHolderNorm_restrict (subset_univ _)).trans_lt hf
    have hh := hb _ (hk i j) F hF hc hsE hfE
    change H2.boundedHolderNorm a (V₀ : Set (ControlCarrier N)) (fun x : ControlCarrier N =>
      H1.principalValueConvolution G C.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K))
        (fun y : Fin N → ℝ => F y) x) ≤
      ENNReal.ofReal (B i j) * H2.boundedHolderNorm a (V₀ : Set (ControlCarrier N)) F
    have hext : H2.boundedHolderNorm a univ F = H2.boundedHolderNorm a (V₀ : Set (ControlCarrier N)) F :=
      boundedHolderNorm_global_eq_of_controlNorm C V₀.isOpen hc hsV
    exact (H2.boundedHolderNorm_restrict hVE).trans
      (hh.trans (mul_le_mul' le_rfl
        ((H2.boundedHolderNorm_restrict (subset_univ E)).trans_eq hext)))

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SourceParameterLinearContinuity
public import RothschildStein.G1.VariationBounds
public import RothschildStein.G1.SmoothDependenceMain

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

/-- Joint continuity of spatial coefficient derivatives pulls back
along an actual jointly continuous flow; no external differentiation occurs. -/
theorem coefficient_derivative_continuousOn_along_flow
    {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set P} {V Ω : Set E} {I : Set ℝ}
    (Z : P → E → E) (Φ : P → E × ℝ → E)
    (hD : ContinuousOn (fun q : P × E => fderiv ℝ (Z q.1) q.2) (U ×ˢ Ω))
    (hΦ : ContinuousOn (fun q : (P × E) × ℝ => Φ q.1.1 (q.1.2, q.2))
      ((U ×ˢ V) ×ˢ I))
    (hrange : ∀ p ∈ U, ∀ x ∈ V, ∀ t ∈ I, Φ p (x, t) ∈ Ω) :
    ContinuousOn
      (fun q : (P × E) × ℝ => fderiv ℝ (Z q.1.1) (Φ q.1.1 (q.1.2, q.2)))
      ((U ×ˢ V) ×ˢ I) := by
  exact hD.comp ((continuous_fst.comp continuous_fst).continuousOn.prodMk hΦ)
    (fun q hq => ⟨hq.1.1, hrange q.1.1 hq.1.1 q.1.2 hq.1.2 q.2 hq.2⟩)

/-- The actual spatial derivative of a family of local flows is
jointly continuous when the spatial coefficient derivatives are jointly
continuous. External parameter derivatives are unnecessary (BB p. 452).
The actual derivative bound follows from the proved Grönwall estimate. -/
theorem localFlow_actual_spatial_derivative_joint_continuousOn
    {P E : Type*} [UniformSpace P] [LocallyCompactSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {U : Set P} {V Ω : Set E} (hU : IsOpen U) (hV : IsOpen V) (hΩ : IsOpen Ω)
    (Z : P → E → E) (Φ : P → E × ℝ → E) {τ T K : ℝ}
    (hτ : 0 < τ) (hT : 0 < T) (hTτ : T < τ) (hK : 0 ≤ K)
    (hZ : ∀ p ∈ U, ContDiffOn ℝ (⊤ : ℕ∞) (Z p) Ω)
    (hc : ∀ p ∈ U, ContinuousOn (Φ p) (V ×ˢ Ioo (-τ) τ))
    (hinit : ∀ p ∈ U, ∀ x ∈ V, Φ p (x, 0) = x)
    (hode : ∀ p ∈ U, ∀ x ∈ V, ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ p (x, v)) (Z p (Φ p (x, t))) t ∧ Φ p (x, t) ∈ Ω)
    (hcoeff : ContinuousOn
      (fun q : (P × E) × ℝ => fderiv ℝ (Z q.1.1) (Φ q.1.1 (q.1.2, q.2)))
      ((U ×ˢ V) ×ˢ Icc (-T) T))
    (hcoeffBound : ∀ p ∈ U, ∀ x ∈ V, ∀ t ∈ Icc (-T) T,
      ‖fderiv ℝ (Z p) (Φ p (x, t))‖ ≤ K) :
    ContinuousOn
      (fun q : (P × E) × ℝ => fderiv ℝ (fun y => Φ q.1.1 (y, q.2)) q.1.2)
      ((U ×ˢ V) ×ˢ Ioo (-T) T) := by
  let A : (P × E) × ℝ → (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) := fun q =>
    ContinuousLinearMap.compL ℝ E E E
      (fderiv ℝ (Z q.1.1) (Φ q.1.1 (q.1.2, q.2)))
  let J : P × E → ℝ → E →L[ℝ] E := fun q t =>
    fderiv ℝ (fun y => Φ q.1 (y, t)) q.2
  have hclosed : Icc (-T) T ⊆ Ioo (-τ) τ := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hsp : ∀ p ∈ U, ContDiffOn ℝ (⊤ : ℕ∞) (Φ p) (V ×ˢ Ioo (-τ) τ) := by
    intro p hp
    exact local_flow_contDiffOn hΩ hV hτ (hZ p hp) (hc p hp) (hinit p hp)
      (fun x hx v hv => ⟨(hode p hp x hx v hv).2, (hode p hp x hx v hv).1⟩)
  have hderivativeBound : ∀ p ∈ U, ∀ x ∈ V, ∀ t ∈ Icc (-T) T,
      ‖fderiv ℝ (fun y => Φ p (y, t)) x‖ ≤ Real.exp (K * T) := by
    intro p hp x hx t ht
    have hs : uIcc 0 t ⊆ Icc (-T) T :=
      ordConnected_Icc.uIcc_subset (show (0 : ℝ) ∈ Icc (-T) T from
        ⟨by linarith, hT.le⟩) ht
    have hb := localFlow_spatial_derivative_bound_of_joint_contDiff hΩ hV (hZ p hp) hτ
      (Φ p) (hsp p hp) (fun y hy => ⟨hinit p hp y hy, hode p hp y hy⟩)
      hx (hclosed ht) hK (fun v hv => hcoeffBound p hp x hx v (hs hv))
    exact hb.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (abs_le.mpr ht) hK))
  have hA : ContinuousOn A ((U ×ˢ V) ×ˢ Icc (-T) T) :=
    (ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn hcoeff
  have hAb : ∀ q ∈ U ×ˢ V, ∀ t ∈ Icc (-T) T, ‖A (q, t)‖ ≤ K := by
    intro q hq t ht
    apply le_trans ((ContinuousLinearMap.compL ℝ E E E).le_opNorm _)
    apply le_trans (mul_le_mul_of_nonneg_right
      (ContinuousLinearMap.norm_compL_le ℝ E E E) (norm_nonneg _))
    simpa only [one_mul] using hcoeffBound q.1 hq.1 q.2 hq.2 t ht
  have hJ : ∀ q ∈ U ×ˢ V, ∀ t ∈ Icc (-T) T,
      HasDerivWithinAt (J q) (A (q, t) (J q t)) (Icc (-T) T) t := by
    intro q hq t ht
    exact (localFlow_variational_of_joint_contDiff hΩ hV (hZ q.1 hq.1)
      (Φ q.1) (hsp q.1 hq.1) (hode q.1 hq.1) hq.2 (hclosed ht)).hasDerivWithinAt
  have hJinit : ∀ q ∈ U ×ˢ V, J q 0 = ContinuousLinearMap.id ℝ E := by
    intro q hq
    have heq : (fun y => Φ q.1 (y, 0)) =ᶠ[𝓝 q.2] id := by
      filter_upwards [hV.mem_nhds hq.2] with y hy
      exact hinit q.1 hq.1 y hy
    exact heq.fderiv_eq.trans fderiv_id
  exact linear_solutions_joint_continuousOn_uniform_parameter (hU.prod hV) hT hK (Real.exp_pos _).le hA hAb hJ
    (fun q hq t ht => hderivativeBound q.1 hq.1 q.2 hq.2 t ht)
    (fun q hq q' hq' => (hJinit q hq).trans (hJinit q' hq').symm)

end RothschildStein.G1

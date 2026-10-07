-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SourceParameterStationaryLift

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G1

/-- Adjoin stationary coefficient coordinates to an actual
parameter flow. Its coefficient and initial-point derivatives are jointly
continuous even when external parameters are only continuous (BB p. 452). -/
theorem parameterFlow_actual_state_derivative_joint_continuousOn
    {P A E : Type*} [UniformSpace P] [LocallyCompactSpace P]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [CompleteSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {U : Set P} {V S : Set (A × E)} (hU : IsOpen U) (hV : IsOpen V) (hS : IsOpen S)
    (W : P → A × E → E) (Φ : P → (A × E) × ℝ → E) {τ T K : ℝ}
    (hτ : 0 < τ) (hT : 0 < T) (hTτ : T < τ) (hK : 0 ≤ K)
    (hW : ∀ σ ∈ U, ContDiffOn ℝ (⊤ : ℕ∞) (W σ) S)
    (hc : ∀ σ ∈ U, ContinuousOn (Φ σ) (V ×ˢ Ioo (-τ) τ))
    (hjoint : ContinuousOn (fun q : (P × (A × E)) × ℝ => Φ q.1.1 (q.1.2, q.2))
      ((U ×ˢ V) ×ˢ Icc (-T) T))
    (hinit : ∀ σ ∈ U, ∀ p ∈ V, Φ σ (p, 0) = p.2)
    (hode : ∀ σ ∈ U, ∀ p ∈ V, ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ σ (p, v)) (W σ (p.1, Φ σ (p, t))) t ∧
        (p.1, Φ σ (p, t)) ∈ S)
    (hD : ContinuousOn (fun q : P × (A × E) => fderiv ℝ (W q.1) q.2) (U ×ˢ S))
    (hDb : ∀ σ ∈ U, ∀ p ∈ V, ∀ t ∈ Icc (-T) T,
      ‖fderiv ℝ (W σ) (p.1, Φ σ (p, t))‖ ≤ K) :
    ContinuousOn
      (fun q : (P × (A × E)) × ℝ => fderiv ℝ (fun p => Φ q.1.1 (p, q.2)) q.1.2)
      ((U ×ˢ V) ×ˢ Ioo (-T) T) := by
  let Z : P → A × E → A × E := fun σ p => (0, W σ p)
  let Ψ : P → (A × E) × ℝ → A × E := fun σ q => (q.1.1, Φ σ q)
  have hZ : ∀ σ ∈ U, ContDiffOn ℝ (⊤ : ℕ∞) (Z σ) S :=
    fun σ hσ => contDiffOn_const.prodMk (hW σ hσ)
  have hΨc : ∀ σ ∈ U, ContinuousOn (Ψ σ) (V ×ˢ Ioo (-τ) τ) :=
    fun σ hσ => (continuous_fst.fst).continuousOn.prodMk (hc σ hσ)
  have hΨjoint : ContinuousOn
      (fun q : (P × (A × E)) × ℝ => Ψ q.1.1 (q.1.2, q.2))
      ((U ×ˢ V) ×ˢ Icc (-T) T) :=
    (continuous_fst.snd.fst).continuousOn.prodMk hjoint
  have hΨinit : ∀ σ ∈ U, ∀ p ∈ V, Ψ σ (p, 0) = p :=
    fun σ hσ p hp => Prod.ext rfl (hinit σ hσ p hp)
  have hΨode : ∀ σ ∈ U, ∀ p ∈ V, ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Ψ σ (p, v)) (Z σ (Ψ σ (p, t))) t ∧ Ψ σ (p, t) ∈ S := by
    intro σ hσ p hp t ht
    exact ⟨(hasDerivAt_const t p.1).prodMk (hode σ hσ p hp t ht).1,
      (hode σ hσ p hp t ht).2⟩
  have hclosed : Icc (-T) T ⊆ Ioo (-τ) τ := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hDZ : ContinuousOn (fun q : P × (A × E) => fderiv ℝ (Z q.1) q.2) (U ×ˢ S) :=
    stationaryLift_fderiv_continuousOn W
      (fun σ hσ p hp => ((hW σ hσ).contDiffAt (hS.mem_nhds hp)).differentiableAt
        (by simp)) hD
  have hcoeff := coefficient_derivative_continuousOn_along_flow Z Ψ hDZ hΨjoint
    (fun σ hσ p hp t ht => (hΨode σ hσ p hp t (hclosed ht)).2)
  have hcoeffBound : ∀ σ ∈ U, ∀ p ∈ V, ∀ t ∈ Icc (-T) T,
      ‖fderiv ℝ (Z σ) (Ψ σ (p, t))‖ ≤ K := by
    intro σ hσ p hp t ht
    exact (stationaryLift_fderiv_norm_le
      (((hW σ hσ).contDiffAt (hS.mem_nhds (hode σ hσ p hp t (hclosed ht)).2)).differentiableAt
        (by simp))).trans (hDb σ hσ p hp t ht)
  have hJ := localFlow_actual_spatial_derivative_joint_continuousOn hU hV hS Z Ψ
    hτ hT hTτ hK hZ hΨc hΨinit hΨode hcoeff hcoeffBound
  let L := ContinuousLinearMap.compL ℝ (A × E) (A × E) E
    (ContinuousLinearMap.snd ℝ A E)
  have hpJ := L.continuous.comp_continuousOn hJ
  apply hpJ.congr
  intro q hq
  have hsp := local_flow_contDiffOn hS hV hτ (hZ q.1.1 hq.1.1) (hΨc q.1.1 hq.1.1)
    (hΨinit q.1.1 hq.1.1)
    (fun p hp v hv => ⟨(hΨode q.1.1 hq.1.1 p hp v hv).2,
      (hΨode q.1.1 hq.1.1 p hp v hv).1⟩)
  have ht : q.2 ∈ Ioo (-τ) τ := hclosed (Ioo_subset_Icc_self hq.2)
  have hd := (((hsp.contDiffAt ((hV.prod isOpen_Ioo).mem_nhds ⟨hq.1.2, ht⟩)).differentiableAt
    (by simp)).hasFDerivAt.comp q.1.2 (hasFDerivAt_prodMk_left q.1.2 q.2))
  have hslice : HasFDerivAt (fun y => Ψ q.1.1 (y, q.2))
      (fderiv ℝ (fun y => Ψ q.1.1 (y, q.2)) q.1.2) q.1.2 :=
    hd.differentiableAt.hasFDerivAt
  exact ((ContinuousLinearMap.snd ℝ A E).hasFDerivAt.comp q.1.2 hslice).fderiv

end RothschildStein.G1

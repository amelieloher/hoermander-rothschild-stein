-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceInduction
public import Mathlib.Analysis.ODE.ExistUnique

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace RothschildStein.G1

/-- Joint regularity on the full open domain of a continuous
local flow (BB Proposition 1.2, p. 3). -/
theorem local_flow_contDiffOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {n : ℕ∞} {Ω U : Set E} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {τ : ℝ} (hτ : 0 < τ) {Z : E → E} (hZ : ContDiffOn ℝ n Z Ω)
    {Φ : (E × ℝ) → E} (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hinit : ∀ x ∈ U, Φ (x, 0) = x)
    (hsol : ∀ x ∈ U, ∀ t ∈ Ioo (-τ) τ,
      Φ (x, t) ∈ Ω ∧ HasDerivAt (fun v => Φ (x, v)) (Z (Φ (x, t))) t) :
    ContDiffOn ℝ n Φ (U ×ˢ Ioo (-τ) τ) := by
  apply contDiffOn_iff_forall_nat_le.mpr
  intro m hm
  exact flowRegularity_nat m hΩ hU hτ (hZ.of_le (by exact_mod_cast hm)) hc hinit hsol

/-- The continuous Picard flow only requires a `C¹` field
(BB Proposition 1.2, p. 3; Mathlib Picard--Lindelöf). -/
theorem exists_continuous_local_flow_of_contDiffOn_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Ω : Set E} (hΩ : IsOpen Ω)
    (Z : E → E) (hZ : ContDiffOn ℝ 1 Z Ω)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ ∃ τ : ℝ, 0 < τ ∧
      ∃ Φ : (E × ℝ) → E,
        ball x₀ r ⊆ Ω ∧ ContinuousOn Φ (ball x₀ r ×ˢ Ioo (-τ) τ) ∧
        ∀ x ∈ ball x₀ r, Φ (x, 0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
          Φ (x, t) ∈ Ω ∧ HasDerivAt (fun v => Φ (x, v)) (Z (Φ (x, t))) t := by
  have hz : ContDiffAt ℝ 1 Z x₀ := hZ.contDiffAt (hΩ.mem_nhds hx₀)
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hz
  obtain ⟨Φ, hΦ, hc⟩ := (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hxball : x₀ ∈ closedBall x₀ (r : ℝ) := mem_closedBall_self hr'.le
  have hΦ₀ : Φ (x₀, 0) = x₀ := (hΦ x₀ hxball).1
  have hc₀ : ContinuousAt Φ (x₀, 0) := hc.continuousAt
    (prod_mem_nhds (closedBall_mem_nhds x₀ hr') (Icc_mem_nhds (by simpa using hε) (by simpa using hε)))
  have hnear : Φ ⁻¹' Ω ∈ 𝓝 (x₀, 0) := hc₀.preimage_mem_nhds (by simpa only [hΦ₀] using hΩ.mem_nhds hx₀)
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.mem_nhds_iff.mp hnear
  let ρ := min δ (min (r : ℝ) ε) / 2
  have hmin : 0 < min δ (min (r : ℝ) ε) := lt_min hδ (lt_min hr' hε)
  have hρ : 0 < ρ := half_pos hmin
  have hρδ : ρ < δ := (half_lt_self hmin).trans_le (min_le_left _ _)
  have hρr : ρ < (r : ℝ) :=
    (half_lt_self hmin).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hρε : ρ < ε :=
    (half_lt_self hmin).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hxt : ∀ x ∈ ball x₀ ρ, ∀ t ∈ Ioo (-ρ) ρ, Φ (x, t) ∈ Ω := by
    intro x hx t ht
    apply hδΩ
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(Metric.mem_ball.mp hx).trans hρδ,
      by rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith [ht.1, ht.2]⟩
  have hxclosed : ∀ x ∈ ball x₀ ρ, x ∈ closedBall x₀ (r : ℝ) :=
    fun x hx => (ball_subset_closedBall.trans (closedBall_subset_closedBall hρr.le)) hx
  have htclosed : Ioo (-ρ) ρ ⊆ Icc (0 - ε) (0 + ε) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨ρ, hρ, ρ, hρ, Φ, ?_, hc.mono (Set.prod_mono hxclosed htclosed), ?_⟩
  · intro x hx
    simpa only [(hΦ x (hxclosed x hx)).1] using hxt x hx 0 (by constructor <;> linarith)
  · intro x hx
    refine ⟨(hΦ x (hxclosed x hx)).1, ?_⟩
    intro t ht
    refine ⟨hxt x hx t ht, ?_⟩
    exact ((hΦ x (hxclosed x hx)).2 t (htclosed ht)).hasDerivAt
      (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))


/-- Existence of a jointly `C^n` local flow, including `n = ∞`
(BB Proposition 1.2, p. 3). -/
theorem exists_contDiff_local_flow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {n : ℕ∞} (hn : 1 ≤ n) {Ω : Set E} (hΩ : IsOpen Ω)
    (Z : E → E) (hZ : ContDiffOn ℝ n Z Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ ∃ τ : ℝ, 0 < τ ∧ ∃ Φ : (E × ℝ) → E,
      ball x₀ r ⊆ Ω ∧ ContDiffOn ℝ n Φ (ball x₀ r ×ˢ Ioo (-τ) τ) ∧
      ∀ x ∈ ball x₀ r, Φ (x, 0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
        Φ (x, t) ∈ Ω ∧ HasDerivAt (fun v => Φ (x, v)) (Z (Φ (x, t))) t := by
  obtain ⟨r, hr, τ, hτ, Φ, hball, hc, hsol⟩ :=
    exists_continuous_local_flow_of_contDiffOn_one hΩ Z
      (hZ.of_le (by exact_mod_cast hn)) hx₀
  exact ⟨r, hr, τ, hτ, Φ, hball,
    local_flow_contDiffOn hΩ isOpen_ball hτ hZ hc
      (fun x hx => (hsol x hx).1) (fun x hx => (hsol x hx).2), hsol⟩

end RothschildStein.G1

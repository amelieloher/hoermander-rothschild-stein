-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderPotentialSolver
public import RothschildStein.H3.CompactControlZeroExtension
public import RothschildStein.H3.FrozenHolderMetricNorm
public import RothschildStein.H3.HolderBoundary
public import RothschildStein.H3.IntrinsicWordRestriction
public import RothschildStein.H3.FrozenDriftEquationRestriction
public import RothschildStein.S.HolderContinuity
public import RothschildStein.H3.QuasiballControlBuffer
public import RothschildStein.H3.QuasiballOriginFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- The actual Hölder potential
solves on a larger ball of the prescribed gauge. The ball and positive
constant precede every source domain and zero-extended source. -/
theorem enlarged_gauge_ball_solver_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (φ : G2.GroupMollifier G C.norm) (ν : G2.HomogeneousNorm G)
    {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1)
    {R : ℝ} (hR : 0 < R) :
    ∃ S : ℝ, R < S ∧ ∃ V : Opens (Fin N → ℝ),
      (∀ x, x ∈ V ↔ ν x < S) ∧ {x | C.norm x < R} ⊆ (V : Set (Fin N → ℝ)) ∧
      ∃ A : ℝ, 0 < A ∧ ∀ Ω : Opens (Fin N → ℝ),
        (Ω : Set (Fin N → ℝ)) ⊆ {x | C.norm x < R} →
        ∀ f : (Fin N → ℝ) → ℝ,
        memHolderXCompact driftWeight H.fields (controlDistance univ driftWeight H.fields) Ω 0 a f →
        (∀ x ∉ Ω, f x = 0) →
        ∃ u : (Fin N → ℝ) → ℝ,
          memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) V 2 a u ∧
          hasDistributionEquationWithDrift V H.fields (fun i => (H.fields_smooth G i).contDiffOn)
            (Distribution.ofFun V u volume (⊤ : ℕ∞)) f ∧
          holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields) V 2 a u ≤
            ENNReal.ofReal A * holderENorm (controlDistance univ driftWeight H.fields) a univ f := by
  classical
  obtain ⟨_b₀, b, _hb₀, hb, hcmp⟩ := G2.gauges_equivalent C.norm.gauge ν.gauge
  let S := max R (b * R) + 1
  have hRS : R < S := by dsimp [S]; linarith [le_max_left R (b * R)]
  have hS : 0 < S := hR.trans hRS
  let V := quasiballDomain G ν 0 S
  have hRV : {x | C.norm x < R} ⊆ (V : Set (Fin N → ℝ)) := by
    rw [quasiballDomain_origin_set]
    intro x hx
    exact ((hcmp x).2.trans_lt (mul_lt_mul_of_pos_left hx hb)).trans
      (by dsimp [S]; linarith [le_max_right R (b * R)])
  obtain ⟨ρ, hρ, hbuffer⟩ := exists_uniform_gauge_ball_buffer G ν C.norm hS
  let B := quasiballDomain G C.norm 0 ρ
  have hVB : (V : Set (Fin N → ℝ)) ⊆ B := hbuffer 0 S le_rfl
  obtain ⟨A, hA, hsolve⟩ := holder_potential_solver_of_controlNorm G H K hQ C φ hρ ha ha1
  refine ⟨S, hRS, V, ?_, hRV, A, hA, ?_⟩
  · intro x
    change x ∈ (V : Set (Fin N → ℝ)) ↔ _
    rw [quasiballDomain_origin_set]
    rfl
  · intro Ω hΩ f hf hz
    have hext : (Ω : Set (Fin N → ℝ)).indicator f = f := by
      funext x
      by_cases hx : x ∈ (Ω : Set (Fin N → ℝ))
      · exact indicator_of_mem hx f
      · rw [indicator_of_notMem hx, hz x hx]
    obtain ⟨hc, hs, hsupport, hn⟩ := continuous_compact_finite_zeroExtension_of_memHolderXCompact
      G driftWeight H.fields (H.fields_smooth G) C Ω 0 (show 0 < (a : ℝ) from ha) hf
    rw [hext] at hc hs hsupport hn
    have hsource : tsupport f ⊆ {x | C.norm x < ρ} := by
      rw [← quasiballDomain_origin_set G C.norm ρ]
      exact hsupport.trans (hΩ.trans (hRV.trans hVB))
    obtain ⟨hu, heq, hnorm⟩ := hsolve f hc hs hsource hn
    let u := G2.groupConvolution G f K
    let D := controlDistanceGeometry_of_controlNorm G driftWeight H.fields C
    have huloc : LocallyIntegrableOn u (B : Set (Fin N → ℝ)) volume :=
      (RothschildStein.S.continuousOn_of_holderENorm_lt_top_on_subset ⊤ D (subset_univ _)
        (show 0 < (a : ℝ) from ha) hu.1).locallyIntegrableOn B.isOpen.measurableSet
    refine ⟨u, memHolderX_restrict_intrinsic driftWeight H.fields
      (controlDistance univ driftWeight H.fields) B V hVB 2 a hu,
      frozen_drift_equation_restrict B V hVB H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) u f huloc heq, ?_⟩
    exact (holderXENorm_restrict_le driftWeight H.fields
      (controlDistance univ driftWeight H.fields) B V hVB 2 a u).trans hnorm

end RothschildStein.H3

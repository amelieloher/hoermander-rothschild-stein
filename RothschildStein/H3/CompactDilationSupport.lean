-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.Gauge
public import RothschildStein.G2.TransposeHomogeneity
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3

/-- Every compact source is supported in the unit gauge ball
at all sufficiently large dilation scales (BB Corollary 8.51, p. 380). -/
theorem exists_unit_ball_dilation_scale {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) {f : (Fin N → ℝ) → ℝ}
    (hf : HasCompactSupport f) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ R : ℝ, R0 ≤ R →
      HasCompactSupport (f ∘ G.dilate R) ∧
      tsupport (f ∘ G.dilate R) ⊆ {x | ν x < 1} := by
  classical
  have hb : ∃ M : ℝ, ∀ x ∈ tsupport f, ν x ≤ M := by
    by_cases hn : (tsupport f).Nonempty
    · obtain ⟨x, hx, hm⟩ := hf.exists_isMaxOn hn ν.gauge.1.continuousOn
      exact ⟨ν x, fun y hy => hm hy⟩
    · exact ⟨0, fun x hx => (hn ⟨x, hx⟩).elim⟩
  obtain ⟨M, hM⟩ := hb
  refine ⟨max M 0 + 1, by have := le_max_right M 0; linarith, ?_⟩
  intro R hR
  have hp : 0 < R := by have := le_max_right M 0; linarith
  have hMR : M < R := by have := le_max_left M 0; linarith
  have hc : HasCompactSupport (f ∘ G.dilate R) :=
    hf.comp_homeomorph (G2.dilationHomeomorph G R hp)
  refine ⟨hc, ?_⟩
  have hs : tsupport (f ∘ G.dilate R) ⊆ G.dilate R ⁻¹' tsupport f := by
    apply closure_minimal
    · intro x hx
      exact subset_closure hx
    · exact isClosed_tsupport f |>.preimage (G2.contDiff_dilate G R).continuous
  intro x hx
  have hbound := hM (G.dilate R x) (hs hx)
  rw [ν.gauge.2.2.2 R hp x] at hbound
  change ν x < 1
  nlinarith

end RothschildStein.H3

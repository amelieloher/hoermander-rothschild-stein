-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.DirectEvaluationSpan
public import RothschildStein.L1.DirectNeighborhoodFreeness
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.L1

/-- In the formal dimension, one free point has a single open
neighborhood of free spanning points (BB Remark 10.18, p. 493). -/
theorem exists_free_spanning_neighborhood {a s N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) (hf : FreeAt p s X x)
    (hd : N = freeDimension a s p) :
    ∃ U : Opens (Fin N → ℝ), x ∈ U ∧ U ≤ Ω ∧
      ∀ y ∈ U, FreeAt p s X y ∧
        Submodule.span ℝ (range (fun I : BoundedWord a s p =>
          wordBracket X (boundedWordList I) y)) = ⊤ := by
  have he := freeAt_eventually_unrestricted Ω X hX hx hf
  obtain ⟨U,hU,hUopen,hxU⟩ := mem_nhds_iff.mp he
  refine ⟨⟨U,hUopen⟩,hxU,?_,?_⟩
  · intro y hy
    exact (hU hy).1
  · intro y hy
    have hh := hU hy
    exact ⟨hh.2,word_span_eq_top_of_freeAt_and_dimension_eq Ω X hX hh.1 hh.2 hd⟩
end RothschildStein.L1

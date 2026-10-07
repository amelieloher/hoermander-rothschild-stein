-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.MollifierAllDimensions

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.S
variable {n : ℕ}

/-- Compact locally integrable inputs have compact smooth
mollifications, including dimension zero (BB Lemma 2.8, pp. 72–73). -/
theorem euclideanRegularize_smooth_compact_all_dimensions
    {f : (Fin n → ℝ) → ℝ} (hf : LocallyIntegrable f volume)
    (hc : HasCompactSupport f) {ε : ℝ} (he : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanRegularize n f ε) ∧
      HasCompactSupport (euclideanRegularize n f ε) := by
  by_cases hn : n = 0
  · subst n
    exact ⟨contDiff_euclideanRegularize_all_dimensions hf he,
      by simpa only [euclideanRegularize_zero_dimension] using hc⟩
  · exact euclideanRegularize_smooth_compact_of_locallyIntegrable
      (Nat.pos_of_ne_zero hn) hf hc he

/-- Compact interior support remains inside an open set for all
sufficiently small positive scales, in every dimension (BB p. 73). -/
theorem exists_euclideanRegularize_support_inside_all_dimensions
    {f : (Fin n → ℝ) → ℝ} (hc : HasCompactSupport f)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hs : tsupport f ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      tsupport (euclideanRegularize n f ε) ⊆ Ω := by
  by_cases hn : n = 0
  · subst n
    exact ⟨1,zero_lt_one,fun ε _ _ =>
      by simpa only [euclideanRegularize_zero_dimension] using hs⟩
  · exact exists_euclideanRegularize_support_inside (Nat.pos_of_ne_zero hn) hc hΩ hs

end RothschildStein.S

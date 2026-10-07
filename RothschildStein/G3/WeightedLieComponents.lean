-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.GradedLayers
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Constant-coefficient combinations of words of exactly weight k
(BB Lemma 9.26, pp. 417–419). -/
def weightedLieLayer {a s : ℕ} (p : Fin a → ℕ+) (k : ℕ) :
    Submodule ℝ (WordCoefficients a s p) :=
  Submodule.span ℝ {f | ∃ I, I ≠ [] ∧ wordWeight p I = k ∧ f = truncatedBracket I}

/-- Homogeneous components of Lie coefficients are combinations of
nested words of the same weight (BB Lemma 9.26, pp. 417–419). -/
theorem weightProjection_mem_weightedLieLayer {a s : ℕ} {p : Fin a → ℕ+}
    (k : ℕ) {f : WordCoefficients a s p} (hf : f ∈ formalSpan a s p) :
    weightProjection k f ∈ weightedLieLayer p k := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨I, hne, _, rfl⟩ := hg
    rw [weightProjection_truncatedBracket]
    split
    · rename_i h
      exact Submodule.subset_span ⟨I, hne, h, rfl⟩
    · exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using (weightedLieLayer p k).zero_mem
  | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul r f _ hf => rw [map_smul]; exact Submodule.smul_mem _ r hf

/-- A lower-order coefficient family has zero projections below its
order (BB Lemma 9.26, pp. 417–419). -/
theorem weightProjection_eq_zero_of_order {a s k l : ℕ} {p : Fin a → ℕ+}
    {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast k f) (hl : l < k) :
    weightProjection l f = 0 := by
  rw [finiteOrderAtLeast_iff] at hf
  funext J
  change (if wordWeight p J.val = l then f J else 0) = 0
  split
  · rename_i he
    exact hf J (he ▸ hl)
  · rfl

/-- Dilation is a polynomial in the real parameter, with each
coefficient its exact homogeneous projection (BB Lemma 9.26, pp. 417–419). -/
theorem finiteDilate_eq_sum_projections {a s : ℕ} {p : Fin a → ℕ+}
    (t : ℝ) (f : WordCoefficients a s p) :
    finiteDilate t f = ∑ k ∈ Finset.range (s + 1), t ^ k • weightProjection k f := by
  conv_lhs => rw [← sum_weightProjection f]
  change dilationLinearMap t _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact finiteDilate_of_projection (by
    rw [weightProjection_comp, ite_eq_left rfl]) t
end RothschildStein.G3

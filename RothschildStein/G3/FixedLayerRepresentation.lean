-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.WeightedLieComponents
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

abbrev LayerWord (a s : ℕ) (p : Fin a → ℕ+) (k : ℕ) :=
  {I : BoundedWord a s p // wordWeight p I.val = k}

theorem layerWord_ne_nil {a s k : ℕ} {p : Fin a → ℕ+} (hk : 1 ≤ k)
    (I : LayerWord a s p k) : I.val.val ≠ [] := by
  intro he
  have hh := I.property
  rw [he] at hh
  simp only [wordWeight, List.map_nil, List.sum_nil] at hh
  omega

theorem weightedLieLayer_eq_span_layerWords {a s k : ℕ} {p : Fin a → ℕ+}
    (hk : 1 ≤ k) (hks : k ≤ s) :
    weightedLieLayer (s := s) p k = Submodule.span ℝ
      (Set.range (fun I : LayerWord a s p k =>
        (truncatedBracket I.val.val : WordCoefficients a s p))) := by
  unfold weightedLieLayer
  congr 1
  ext f
  constructor
  · rintro ⟨I,hI,hw,rfl⟩
    exact ⟨⟨boundedWord p I (hw ▸ hks),hw⟩,rfl⟩
  · rintro ⟨I,rfl⟩
    exact ⟨I.val.val,layerWord_ne_nil hk I,I.property,rfl⟩

/-- Homogeneous coefficients use one slot for each bounded word in the layer. -/
theorem weightedLieLayer_fixed_representation {a s k : ℕ} {p : Fin a → ℕ+}
    (hk : 1 ≤ k) (hks : k ≤ s) {f : WordCoefficients a s p}
    (hf : f ∈ weightedLieLayer p k) :
    ∃ c : LayerWord a s p k → ℝ,
      ∑ I, c I • (truncatedBracket I.val.val : WordCoefficients a s p) = f := by
  classical
  rw [weightedLieLayer_eq_span_layerWords hk hks] at hf
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).mp hf
end RothschildStein.G3

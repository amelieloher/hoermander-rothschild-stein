-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FixedLayerRepresentation
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- The fixed finite word frame has a numerical bounded right inverse. -/
theorem exists_bounded_layer_representation {a s k : ℕ} {p : Fin a → ℕ+}
    (hk : 1 ≤ k) (hks : k ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : weightedLieLayer (s := s) p k,
      ∃ c : LayerWord a s p k → ℝ,
        (∑ I, c I • (truncatedBracket I.val.val : WordCoefficients a s p) = f.val) ∧
        ‖c‖ ≤ C*‖f.val‖ := by
  classical
  let v : LayerWord a s p k → weightedLieLayer (s := s) p k := fun I =>
    ⟨truncatedBracket I.val.val,Submodule.subset_span
      ⟨I.val.val,layerWord_ne_nil hk I,I.property,rfl⟩⟩
  let L := Fintype.linearCombination ℝ v
  have hsurj : Function.Surjective L := by
    intro f
    obtain ⟨c,hc⟩ := weightedLieLayer_fixed_representation hk hks f.property
    refine ⟨c,?_⟩
    apply Subtype.ext
    simpa [L,Fintype.linearCombination_apply,v] using hc
  obtain ⟨J,hJ⟩ := L.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  let Jc := J.toContinuousLinearMap
  refine ⟨1+‖Jc‖,by positivity,?_⟩
  intro f
  refine ⟨J f,?_,?_⟩
  · have he : L (J f) = f := LinearMap.congr_fun hJ f
    have hv := congrArg Subtype.val he
    simpa [L,Fintype.linearCombination_apply,v] using hv
  · have he := Jc.le_opNorm f
    exact he.trans (mul_le_mul_of_nonneg_right (by linarith [norm_nonneg Jc]) (norm_nonneg f))
end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.FieldGermExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- An interior compact set has a global smooth
compactly supported field with the original field's germs there.
This strengthens the existing germ extension by one test cutoff
(BB Prop 2.22, pp. 88–90; compact-flow reduction). -/
theorem exists_compact_global_field_germ_extension
    (Ω : Opens (Fin n → ℝ)) (K : Compacts (Fin n → ℝ))
    (hK : (K : Set (Fin n → ℝ)) ⊆ Ω)
    (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X (Ω : Set (Fin n → ℝ))) :
    ∃ B : (Fin n → ℝ) → (Fin n → ℝ),ContDiff ℝ (⊤ : ℕ∞) B ∧
      HasCompactSupport B ∧ ∀ x ∈ (K : Set (Fin n → ℝ)),B =ᶠ[𝓝 x] X := by
  obtain ⟨V,hV,hG⟩ := exists_global_field_germ_extension Ω K hK X hX
  obtain ⟨χ,U,hU,hKU,_,hone⟩ := exists_test_plateau Ω K hK
  refine ⟨fun x => χ x • V x,χ.contDiff.smul hV,?_,?_⟩
  · simpa only [Pi.smul_apply'] using! (χ.hasCompactSupport.smul_right (f' := V))
  · intro x hx
    filter_upwards [hU.mem_nhds (hKU hx),hG x hx] with y hy hgy
    have hχ : χ y = (1 : ℝ) := hone hy
    rw [hχ,hgy,one_smul]

end RothschildStein.S

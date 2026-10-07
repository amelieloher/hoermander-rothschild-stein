-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FreeCanonicalCharts
public import RothschildStein.G4.ShortFields
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- The canonical model basis is selected from the actual finite short words. -/
def canonicalShortWord {a s : ℕ} {p : Fin a → ℕ+} (D : G3.FreeModelData a s p)
    (j : Fin (freeDimension a s p)) : G4.ShortWord p s :=
  ⟨G3.modelBasisWord D j, (G4.mem_shortWordFamily_iff p _).mpr
    ⟨(G3.modelBasisWord_spec D j).1,(G3.modelBasisWord_spec D j).2.1⟩⟩

/-- Distinct basis coordinates correspond to distinct short words. -/
theorem canonicalShortWord_injective {a s : ℕ} {p : Fin a → ℕ+}
    (D : G3.FreeModelData a s p) : Function.Injective (canonicalShortWord D) := by
  intro j k h
  apply D.basis.injective
  apply Subtype.ext
  rw [(G3.modelBasisWord_spec D j).2.2,(G3.modelBasisWord_spec D k).2.2]
  exact congrArg truncatedBracket (congrArg Subtype.val h)

/-- Canonical short-word weights equal the model's homogeneous weights. -/
theorem canonicalShortWord_weight {a s : ℕ} {p : Fin a → ℕ+}
    (D : G3.FreeModelData a s p) (j : Fin (freeDimension a s p)) :
    (G4.shortWeight p (canonicalShortWord D j) : ℕ) = D.group.weight j := by
  change wordWeight p (G3.modelBasisWord D j) = D.weight j
  exact G3.modelBasisWord_weight D j

/-- The canonical frame evaluates the same actual short bracket fields. -/
theorem canonicalWordFrame_eq_shortField {a s : ℕ} {p : Fin a → ℕ+}
    (D : G3.FreeModelData a s p)
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ)) (j : Fin (freeDimension a s p)) :
    canonicalWordFrame D X j = G4.shortField p X (canonicalShortWord D j) := rfl
end RothschildStein.L1

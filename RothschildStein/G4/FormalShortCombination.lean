-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G3.NormalizedTargetFields
public import RothschildStein.G3.EnumeratedWordUniqueness
public import RothschildStein.G4.ShortFields

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Classical
open scoped BigOperators
namespace RothschildStein.G4
open G3

/-- The retained-word enumeration is exactly the actual
short-field index family, with no multiplicity (BB p. 459). -/
theorem correctionWordEnumeration_toFinset_eq_shortWordFamily {m s : ℕ}
    (w : Fin m → ℕ+) :
    (correctionWordEnumeration m s w s).toFinset = shortWordFamily w s := by
  ext I
  rw [List.mem_toFinset, mem_shortWordFamily_iff]
  exact ⟨correctionWordEnumeration_mem I,
    fun h => correctionWordEnumeration_contains I h.1 h.2 h.2⟩

/-- Coefficients on actual short fields, extended by zero to other words. -/
def shortWordCoefficients {m s : ℕ} {w : Fin m → ℕ+}
    (a : ShortWord w s → ℝ) (I : List (Fin m)) : ℝ :=
  if h : I ∈ shortWordFamily w s then a ⟨I, h⟩ else 0

/-- The formal target evaluates to the actual constant
linear combination of all short bracket fields on the original domain. -/
theorem finiteLieField_short_combination {m n s : ℕ} {w : Fin m → ℕ+}
    (D : FreeModelData m s w) (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (a : ShortWord w s → ℝ) {x : Fin n → ℝ} (hx : x ∈ Ω) :
    finiteLieField D X (normalizedWordTarget (shortWordCoefficients a)) x =
      ∑ I : ShortWord w s, a I • shortField w X I x := by
  rw [finiteLieField_normalizedWordTarget D Ω X hX _ hx,
    ← List.sum_toFinset _ (correctionWordEnumeration_nodup m s w s),
    correctionWordEnumeration_toFinset_eq_shortWordFamily,
    ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro I _
  simp only [shortWordCoefficients, dite_eq_left I.property, shortField]

/-- The actual constant controls satisfy precisely the retained
coefficient budget requested by the primitive approximation provider. -/
theorem shortWordCoefficients_weighted_bound {m s : ℕ} {w : Fin m → ℕ+}
    (a : ShortWord w s → ℝ) (δ : ℝ)
    (ha : ∀ I, |a I| ≤ δ ^ (shortWeight w I : ℕ)) :
    ∀ I ∈ correctionWordEnumeration m s w s,
      |shortWordCoefficients a I| ≤ δ ^ wordWeight w I := by
  intro I hI
  have hm : I ∈ shortWordFamily w s :=
    (mem_shortWordFamily_iff w I).mpr (correctionWordEnumeration_mem I hI)
  have hh := ha ⟨I, hm⟩
  change |a ⟨I, hm⟩| ≤ δ ^ wordWeight w I at hh
  simpa only [shortWordCoefficients, dite_eq_left hm] using hh

end RothschildStein.G4

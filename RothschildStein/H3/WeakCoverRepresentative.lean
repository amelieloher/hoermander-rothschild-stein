-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompatibleCoverRepresentative
public import RothschildStein.S.WeakDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
variable {n m : ℕ}

/-- Uniqueness of weak derivatives supplies the overlap compatibility
needed to select one representative across an open exhaustion. -/
theorem weakWord_cover_compatible
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin m))
    (U : ℕ → Opens (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (g : ℕ → (Fin n → ℝ) → ℝ)
    (hg : ∀ i, hasWeakWordDeriv X (U i) I f (g i)) :
    ∀ i j, g i =ᵐ[volume.restrict ((U i : Set (Fin n → ℝ)) ∩ U j)] g j := by
  intro i j
  have hi := S.hasWeakWordDeriv_restrict X (U i) (U i ⊓ U j)
    (by intro x hx; exact hx.1) (hg i)
  have hj := S.hasWeakWordDeriv_restrict X (U j) (U i ⊓ U j)
    (by intro x hx; exact hx.2) (hg j)
  exact S.hasWeakWordDeriv_unique X (U i ⊓ U j) hi hj

/-- The selected compatible function is an actual weak derivative on every
patch, without assuming global integrability or global weak regularity. -/
theorem coverRepresentative_hasWeakWordDeriv
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin m))
    (U : ℕ → Opens (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (g : ℕ → (Fin n → ℝ) → ℝ)
    (hcover : ∀ x, ∃ i, x ∈ (U i : Set (Fin n → ℝ)))
    (hg : ∀ i, hasWeakWordDeriv X (U i) I f (g i)) (i : ℕ) :
    hasWeakWordDeriv X (U i) I f
      (coverRepresentative (fun j => (U j : Set (Fin n → ℝ))) g hcover) := by
  have he := coverRepresentative_ae_eq (volume : Measure (Fin n → ℝ))
    (fun j => (U j : Set (Fin n → ℝ))) g hcover
    (fun j => (U j).isOpen.measurableSet) (weakWord_cover_compatible X I U f g hg) i
  exact S.hasWeakWordDeriv_congr_ae X (U i) (hg i) ae_eq_rfl he.symm

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.SobolevAE

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal
namespace RothschildStein.S
variable {n q : ℕ}

/-- The zero-boundary Sobolev predicate is invariant
under equality almost everywhere on its domain (BB Def 2.2, p. 68). -/
theorem memSobolevXZero_congr_ae
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Opens (Fin n → ℝ))
    (w : Fin q → ℕ+) (k : ℕ) (p : ℝ≥0∞) {f g : (Fin n → ℝ) → ℝ}
    (h : f =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] g) :
    memSobolevXZero w X Ω k p f ↔ memSobolevXZero w X Ω k p g := by
  constructor
  · rintro ⟨hf,φ,ht⟩
    refine ⟨(memSobolevX_congr_ae X Ω w k p h).mp hf,φ,?_⟩
    exact ht.congr (fun j => sobolevXENorm_congr_ae X Ω w k p (h.sub ae_eq_rfl))
  · rintro ⟨hg,φ,ht⟩
    refine ⟨(memSobolevX_congr_ae X Ω w k p h).mpr hg,φ,?_⟩
    exact ht.congr (fun j => sobolevXENorm_congr_ae X Ω w k p (h.symm.sub ae_eq_rfl))

end RothschildStein.S

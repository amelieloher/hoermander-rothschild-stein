-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffGlobalNorm
public import RothschildStein.H3.CutoffSquareNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- The global cutoff square is bounded by local input jets with
explicit cutoff derivative constants (BB (8.54), p. 371). -/
theorem cutoff_square_global_le_of_bounds {n m : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (i : Fin m) (u g h : (Fin n → ℝ) → ℝ)
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (hg : hasWeakWordDeriv X Ω [i] u g)
    (hh : hasWeakWordDeriv X Ω [i,i] u h)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (A B : ℝ≥0∞)
    (hφ : eLpNorm φ ⊤ (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ 1)
    (hA : eLpNorm (fieldDerivative (X i) φ) ⊤
      (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ A)
    (hB : eLpNorm (fieldDerivative (X i) (fieldDerivative (X i) φ)) ⊤
      (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ B) :
    weakWordENorm X ⊤ [i,i] p (fun x => u x * φ x) ≤
      weakWordENorm X Ω [i,i] p u +
      2 * A * weakWordENorm X Ω [i] p u +
      B * eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
  have hw := S.hasWeakWordDeriv_mul_square X Ω hX i u g h φ φ.contDiff.contDiffOn hg hh
  rw [cutoff_weakNorm_global_eq_local X Ω [i,i] p u _ φ hw,
    S.weakWordENorm_eq X Ω [i,i] p u h hh,
    S.weakWordENorm_eq X Ω [i] p u g hg]
  have hb := cutoff_square_weakNorm_le X Ω hX i u g h φ φ.contDiff.contDiffOn hg hh p hp
  have hn : weakWordENorm X Ω [i,i] p (fun x => u x * φ x) ≤
      1 * eLpNorm h p (volume.restrict (Ω : Set (Fin n → ℝ))) +
      2 * (A * eLpNorm g p (volume.restrict (Ω : Set (Fin n → ℝ)))) +
      B * eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
    exact hb.trans (by gcongr)
  simpa only [one_mul, mul_assoc] using hn

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Leibniz
public import RothschildStein.S.Sobolev
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory TopologicalSpace
open scoped ENNReal

/-- Quantitative weak square product rule with the exact coefficient
2 on the first-derivative term (BB (8.54), p. 371). -/
theorem cutoff_square_weakNorm_le {n m : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (i : Fin m) (u g h φ : (Fin n → ℝ) → ℝ)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ (Ω : Set (Fin n → ℝ)))
    (hg : hasWeakWordDeriv X Ω [i] u g)
    (hh : hasWeakWordDeriv X Ω [i,i] u h)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    weakWordENorm X Ω [i,i] p (fun x => u x * φ x) ≤
      eLpNorm φ ⊤ (volume.restrict (Ω : Set (Fin n → ℝ))) *
        eLpNorm h p (volume.restrict (Ω : Set (Fin n → ℝ))) +
      2 * (eLpNorm (fieldDerivative (X i) φ) ⊤ (volume.restrict (Ω : Set (Fin n → ℝ))) *
        eLpNorm g p (volume.restrict (Ω : Set (Fin n → ℝ)))) +
      eLpNorm (fieldDerivative (X i) (fieldDerivative (X i) φ)) ⊤
        (volume.restrict (Ω : Set (Fin n → ℝ))) *
        eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
  let μ := volume.restrict (Ω : Set (Fin n → ℝ))
  have hp0 : 0 < p := lt_of_lt_of_le (by simp) hp
  rw [S.weakWordENorm_eq X Ω [i,i] p _ _
    (S.hasWeakWordDeriv_mul_square X Ω hX i u g h φ hφ hg hh)]
  have hmul (a b : (Fin n → ℝ) → ℝ) :
      eLpNorm (fun x => b x * a x) p μ ≤ eLpNorm a ⊤ μ * eLpNorm b p μ := by
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_def, mul_comm] using
      (eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos p hp0
        (φ := a) (f := b) (μ := μ))
  have htwo : eLpNorm (fun x => 2 * g x * fieldDerivative (X i) φ x) p μ ≤
      2 * (eLpNorm (fieldDerivative (X i) φ) ⊤ μ * eLpNorm g p μ) := by
    have he : (fun x => 2 * g x * fieldDerivative (X i) φ x) =
        (2 : ℝ) • (fun x => g x * fieldDerivative (X i) φ x) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, eLpNorm_const_smul]
    have hb := hmul (fieldDerivative (X i) φ) g
    simpa [Real.enorm_eq_ofReal_abs] using (show (‖(2 : ℝ)‖ₑ) * eLpNorm (fun x => g x * fieldDerivative (X i) φ x) p μ ≤
      (‖(2 : ℝ)‖ₑ) * (eLpNorm (fieldDerivative (X i) φ) ⊤ μ * eLpNorm g p μ) from by gcongr)
  exact (eLpNorm_add_le hp).trans (add_le_add
    ((eLpNorm_add_le hp).trans (add_le_add (hmul φ h) htwo))
    (hmul (fieldDerivative (X i) (fieldDerivative (X i) φ)) u))

end RothschildStein.H3

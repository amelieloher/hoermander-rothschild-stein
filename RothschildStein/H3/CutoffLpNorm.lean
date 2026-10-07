-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffSobolevGlobal
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- Multiplication by a cutoff bounded by one does not increase the local-to-global Lp norm
(BB Lemma 8.42, p. 371). -/
theorem cutoff_eLpNorm_le {n : ℕ} (Ω : Opens (Fin n → ℝ))
    (u : (Fin n → ℝ) → ℝ) (φ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (p : ℝ≥0∞) (hp : 0 < p)
    (hφ : eLpNorm φ ⊤ (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ 1) :
    eLpNorm (fun x => u x * φ x) p volume ≤
      eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
  have he : (Ω : Set (Fin n → ℝ)).indicator (fun x => u x * φ x) =
      fun x => u x * φ x := by
    funext x
    by_cases hx : x ∈ (Ω : Set (Fin n → ℝ))
    · simp [hx]
    · simp [hx, φ.zero_on_compl hx]
  rw [← he, S.eLpNorm_zeroExtension Ω.isOpen.measurableSet]
  have hb := eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos p hp
    (φ := (φ : (Fin n → ℝ) → ℝ)) (f := u)
    (μ := volume.restrict (Ω : Set (Fin n → ℝ)))
  have hb' : eLpNorm (fun x => u x * φ x) p (volume.restrict (Ω : Set (Fin n → ℝ))) ≤
      eLpNorm φ ⊤ (volume.restrict (Ω : Set (Fin n → ℝ))) *
        eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_def, mul_comm] using hb
  exact hb'.trans (by simpa only [one_mul] using mul_le_mul' hφ (le_refl
    (eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ))))))

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DriftCutoffGlobalNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- A test cutoff with supremum at most one bounds the global
product norm by the original input's local norm, including p infinity.
The exterior values of the input are unrestricted. -/
theorem cutoff_product_global_norm_le {N : ℕ}
    (U : Opens (Fin N → ℝ)) (p : ℝ≥0∞) (hp : 0 < p)
    (u : (Fin N → ℝ) → ℝ) (φ : TestFunction U ℝ (⊤ : ℕ∞))
    (hφ : eLpNorm φ ⊤ (volume.restrict (U : Set (Fin N → ℝ))) ≤ 1) :
    eLpNorm (fun x => u x * φ x) p volume ≤
      eLpNorm u p (volume.restrict (U : Set (Fin N → ℝ))) := by
  have he : (U : Set (Fin N → ℝ)).indicator (fun x => u x * φ x) =
      (fun x => u x * φ x) := by
    funext x
    by_cases hx : x ∈ (U : Set (Fin N → ℝ))
    · exact indicator_of_mem hx _
    · simp only [indicator_of_notMem hx, φ.zero_on_compl hx, Pi.zero_apply, mul_zero]
  rw [← he, eLpNorm_indicator_eq_eLpNorm_restrict U.isOpen.measurableSet]
  have hb := eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos p hp
    (φ := (φ : (Fin N → ℝ) → ℝ)) (f := u)
    (μ := volume.restrict (U : Set (Fin N → ℝ)))
  have hb' : eLpNorm (fun x => u x * φ x) p (volume.restrict (U : Set (Fin N → ℝ))) ≤
      eLpNorm φ ⊤ (volume.restrict (U : Set (Fin N → ℝ))) *
        eLpNorm u p (volume.restrict (U : Set (Fin N → ℝ))) := by
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_def, mul_comm] using hb
  exact hb'.trans (by simpa only [one_mul] using (mul_le_mul' hφ
    (le_refl (eLpNorm u p (volume.restrict (U : Set (Fin N → ℝ)))))))

end RothschildStein.H3

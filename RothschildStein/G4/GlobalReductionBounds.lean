-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.MatrixMagnitudeBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- A frame nondegeneracy lower bound gives the exact squared
lower bound for the global denominator (BB Lemma 9.31, pp. 422–423). -/
theorem determinantSquareSum_lower_bound {ι : Type*} [Fintype ι] {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) (hframe : ∃ B : Fin n → ι, Δ ≤ |frameDet Z B x|) :
    Δ ^ 2 ≤ determinantSquareSum Z x := by
  classical
  obtain ⟨B, hB⟩ := hframe
  have hs : Δ ^ 2 ≤ (frameDet Z B x) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hΔ (abs_nonneg _)).mpr hB
  exact hs.trans (Finset.single_le_sum (fun C _ => sq_nonneg (frameDet Z C x)) (Finset.mem_univ B))

end RothschildStein.G4

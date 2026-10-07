-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.BracketJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Directional derivatives consume one scalar coefficient jet,
with an explicit universal bilinear factor. -/
theorem HasJetBound.fieldDerivative {n : ℕ} {Ω K : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {Z : (Fin n → ℝ) → (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    {h : ℕ} {P C : ℝ} (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hZP : HasJetBound Ω K Z h P) (hfC : HasJetBound Ω K f (h + 1) C) :
    HasJetBound Ω K (fieldDerivative Z f) h (2 ^ h * C * P) := by
  have hdf : ContDiffOn ℝ (⊤ : ℕ∞) (_root_.fderiv ℝ f) Ω := hf.fderiv_of_isOpen hΩ (by simp)
  have hdfC := hfC.fderiv hΩ hKΩ
  intro j hj x hx
  have hb := norm_iteratedFDerivWithin_clm_apply hdf hZ hΩ.uniqueDiffOn (hKΩ hx)
    (n := j) (by simp)
  apply hb.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * C * P := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hdfC i ((Finset.mem_range_succ_iff.mp hi).trans hj) x hx)
          (by positivity))
        (hZP (j - i) ((Nat.sub_le j i).trans hj) x hx) (norm_nonneg _)
        (mul_nonneg (by positivity) hC)
    _ = (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * C * P := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = 2 ^ j * C * P := by
      have he : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [he]
    _ ≤ 2 ^ h * C * P := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hC) hP

end RothschildStein.G4

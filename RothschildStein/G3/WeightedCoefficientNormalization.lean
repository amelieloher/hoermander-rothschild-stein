-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.NormalizedTargetDilation
public import RothschildStein.G3.DilatedInputCoordinates
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

/-- Normalize a source coefficient by its positive weighted radius. -/
def normalizeWordCoefficients {a : ℕ} (p : Fin a → ℕ+) (δ : ℝ)
    (c : List (Fin a) → ℝ) (I : List (Fin a)) : ℝ := c I / δ^wordWeight p I

theorem abs_normalizeWordCoefficients_le_one {a : ℕ} {p : Fin a → ℕ+}
    {δ : ℝ} (hδ : 0 < δ) (c : List (Fin a) → ℝ) (I : List (Fin a))
    (hc : |c I| ≤ δ^wordWeight p I) : |normalizeWordCoefficients p δ c I| ≤ 1 := by
  rw [normalizeWordCoefficients,abs_div,abs_of_pos (pow_pos hδ _)]
  exact (div_le_one (pow_pos hδ _)).mpr hc

/-- The dilated normalized formal target is the original source target. -/
theorem retainedLieDilation_normalized_source {a s : ℕ} {p : Fin a → ℕ+}
    {δ : ℝ} (hδ : 0 < δ) (c : List (Fin a) → ℝ) :
    retainedLieDilation δ (normalizedWordTarget (s := s) (p := p)
      (normalizeWordCoefficients p δ c)) = normalizedWordTarget (s := s) (p := p) c := by
  rw [retainedLieDilation_normalizedWordTarget]
  congr 1
  funext I
  dsimp [normalizeWordCoefficients]
  have hne : δ^wordWeight p I ≠ 0 := ne_of_gt (pow_pos hδ _)
  field_simp

/-- Source target coordinates agree with the coefficient dilation used by the flow provider. -/
theorem dilatedInputCoordinates_normalized_source {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) {δ : ℝ} (hδ : 0 < δ) (c : List (Fin a) → ℝ) :
    dilatedInputCoordinates D (normalizedWordTarget (s := s) (p := p)
      (normalizeWordCoefficients p δ c)) δ = D.basis.equivFun (normalizedWordTarget c) := by
  have he := dilatedInputCoordinates_eq D
    (normalizedWordTarget (s := s) (p := p) (normalizeWordCoefficients p δ c)) δ
  exact he.trans (congrArg D.basis.equivFun (retainedLieDilation_normalized_source hδ c))
end RothschildStein.G3

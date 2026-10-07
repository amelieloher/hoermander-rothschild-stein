-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.SmoothCompactLipschitz
public import RothschildStein.S.LipschitzHolderNorm
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n q : ℕ}

/-- Smooth compact data belong to the exact scalar
Hölder class on any local comparison patch
(BB (2.15), p. 81; compact smooth inclusion). -/
theorem holderENorm_lt_top_of_smooth_compact_comparison
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (V : Set (Fin n → ℝ)) {κ α : ℝ} (hκ : DistanceComparison d V κ)
    (hα : 0 < α) (hα1 : α ≤ 1)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    holderENorm d α V f < ⊤ := by
  obtain ⟨Λ,hΛ,hLip⟩ := exists_lipschitz_constant_of_smooth_compact hf hc
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hf.continuous
  exact holderENorm_lt_top_of_lipschitz_comparison d V f hκ hΛ hα hα1
    (ENNReal.ofReal M) ENNReal.ofReal_lt_top
    (fun x _ => ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using hM x))
    (fun x _ y _ => hLip x y)

/-- Every word of locally smooth fields applied to an
interior test has finite Hölder norm on a comparison patch;
no global coefficient smoothness is imposed
(BB (2.15), p. 81; local test-word inclusion). -/
theorem holderENorm_word_test_lt_top
    (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i,ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (V : Set (Fin n → ℝ)) {κ α : ℝ} (hκ : DistanceComparison d V κ)
    (hα : 0 < α) (hα1 : α ≤ 1) (I : List (Fin q))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    holderENorm d α V (wordDerivative X I φ) < ⊤ :=
  holderENorm_lt_top_of_smooth_compact_comparison d V hκ hα hα1
    (wordDerivativeTest Ω X hX I φ).contDiff (wordDerivativeTest Ω X hX I φ).hasCompactSupport

end RothschildStein.S

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.LipschitzHolderComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.S
variable {n : ℕ}

/-- The full Hölder norm is finite for bounded
Euclidean Lipschitz data on a comparison patch
(BB (2.15), p. 81; full-norm assembly). -/
theorem holderENorm_lt_top_of_lipschitz_comparison
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (V : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    {κ Λ α : ℝ} (hκ : DistanceComparison d V κ)
    (hΛ : 0 ≤ Λ) (hα : 0 < α) (hα1 : α ≤ 1)
    (M : ℝ≥0∞) (hM : M < ⊤) (hb : ∀ x ∈ V,ENNReal.ofReal |f x| ≤ M)
    (hl : ∀ x ∈ V,∀ y ∈ V,|f x-f y| ≤ Λ*‖x-y‖) :
    holderENorm d α V f < ⊤ := by
  have hs : (⨆ x : V,ENNReal.ofReal |f x.val|) ≤ M := iSup_le (fun x => hb x.val x.property)
  have hn := holderSeminorm_le_of_lipschitz_comparison d V f hκ hΛ hα hα1 M hM hb hl
  have ht : (2*M)^(1-α)*(ENNReal.ofReal (κ*Λ))^α < ⊤ :=
    ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hα1) (ENNReal.mul_lt_top (by norm_num) hM).ne)
      (ENNReal.rpow_lt_top_of_nonneg hα.le ENNReal.ofReal_ne_top)
  exact ENNReal.add_lt_top.mpr ⟨lt_of_le_of_lt hs hM,lt_of_le_of_lt hn ht⟩

end RothschildStein.S

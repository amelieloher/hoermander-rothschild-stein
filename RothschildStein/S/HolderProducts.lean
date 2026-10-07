-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.S
variable {n : ℕ}

/-- The product seminorm estimate with the exact norms
(BB (2.20), p. 84). Both inputs belong to the Hölder class. -/
theorem holderSeminorm_mul_le
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) {α : ℝ} (hα : 0 < α)
    (V : Set (Fin n → ℝ)) (hsep : ∀ x ∈ V, ∀ y ∈ V, d x y = 0 → x = y)
    (f g : (Fin n → ℝ) → ℝ)
    (hf : holderENorm d α V f < ⊤) (hg : holderENorm d α V g < ⊤) :
    holderSeminorm d α V (fun x => f x*g x) ≤
      holderSeminorm d α V f*(⨆ x : V,ENNReal.ofReal |g x.val|) +
      holderSeminorm d α V g*(⨆ x : V,ENNReal.ofReal |f x.val|) := by
  have hfN : (⨆ x : V,ENNReal.ofReal |f x.val|) < ⊤ := lt_of_le_of_lt le_self_add hf
  have hgN : (⨆ x : V,ENNReal.ofReal |g x.val|) < ⊤ := lt_of_le_of_lt le_self_add hg
  have hfS : holderSeminorm d α V f < ⊤ := lt_of_le_of_lt le_add_self hf
  have hgS : holderSeminorm d α V g < ⊤ := lt_of_le_of_lt le_add_self hg
  apply holderSeminorm_le_of_bound
  · exact ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top hfS hgN,ENNReal.mul_lt_top hgS hfN⟩
  · intro x hx y hy hxy
    have hr : |f x*g x-f y*g y| ≤ |f x-f y| *|g x| +|g x-g y| *|f y| := by
      calc
        _ = |(f x-f y)*g x+(g x-g y)*f y| := by congr 1; ring
        _ ≤ _ := by simpa only [abs_mul] using abs_add_le ((f x-f y)*g x) ((g x-g y)*f y)
    have hfx := holderSeminorm_increment_le d α V f hα hsep hx hy hxy
    have hgx := holderSeminorm_increment_le d α V g hα hsep hx hy hxy
    have hfy : ENNReal.ofReal |f y| ≤ ⨆ z : V,ENNReal.ofReal |f z.val| :=
      le_iSup_of_le ⟨y,hy⟩ le_rfl
    have hgy : ENNReal.ofReal |g x| ≤ ⨆ z : V,ENNReal.ofReal |g z.val| :=
      le_iSup_of_le ⟨x,hx⟩ le_rfl
    calc
      _ ≤ ENNReal.ofReal (|f x-f y| *|g x| +|g x-g y| *|f y|) := ENNReal.ofReal_le_ofReal hr
      _ = ENNReal.ofReal |f x-f y| *ENNReal.ofReal |g x| +
          ENNReal.ofReal |g x-g y| *ENNReal.ofReal |f y| := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (abs_nonneg _),ENNReal.ofReal_mul (abs_nonneg _)]
      _ ≤ (holderSeminorm d α V f*(d x y)^α)*(⨆ z : V,ENNReal.ofReal |g z.val|)+
          (holderSeminorm d α V g*(d x y)^α)*(⨆ z : V,ENNReal.ofReal |f z.val|) :=
        add_le_add (mul_le_mul' hfx hgy) (mul_le_mul' hgx hfy)
      _ = _ := by ring

/-- The full product estimate has constant one, as in BB
(2.21), p. 84. It also proves closure under multiplication. -/
theorem holderENorm_mul_le
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) {α : ℝ} (hα : 0 < α)
    (V : Set (Fin n → ℝ)) (hsep : ∀ x ∈ V, ∀ y ∈ V, d x y = 0 → x = y)
    (f g : (Fin n → ℝ) → ℝ)
    (hf : holderENorm d α V f < ⊤) (hg : holderENorm d α V g < ⊤) :
    holderENorm d α V (fun x => f x*g x) ≤ holderENorm d α V f*holderENorm d α V g := by
  have hs := holderSeminorm_mul_le d hα V hsep f g hf hg
  have hn : (⨆ x : V,ENNReal.ofReal |f x.val*g x.val|) ≤
      (⨆ x : V,ENNReal.ofReal |f x.val|)*(⨆ x : V,ENNReal.ofReal |g x.val|) := by
    apply iSup_le
    intro x
    rw [abs_mul,ENNReal.ofReal_mul (abs_nonneg _)]
    exact mul_le_mul' (le_iSup (fun z : V => ENNReal.ofReal |f z.val|) x)
      (le_iSup (fun z : V => ENNReal.ofReal |g z.val|) x)
  apply (add_le_add hn hs).trans
  unfold holderENorm
  calc
    _ ≤ _+holderSeminorm d α V f*holderSeminorm d α V g := le_self_add
    _ = _ := by ring

end RothschildStein.S

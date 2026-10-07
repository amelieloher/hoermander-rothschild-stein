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
variable (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (α : ℝ)
variable (V : Set (Fin n → ℝ))

/-- Negation preserves the exact Hölder seminorm
(BB Def 2.13 and Prop 2.15, pp. 81–82). -/
theorem holderSeminorm_neg (f : (Fin n → ℝ) → ℝ) :
    holderSeminorm d α V (fun x => -f x) = holderSeminorm d α V f := by
  unfold holderSeminorm
  congr 1
  ext C
  constructor <;> rintro ⟨hc,hb⟩ <;> refine ⟨hc,fun x hx y hy hd => ?_⟩
  · simpa only [neg_sub_neg,abs_sub_comm] using! hb x hx y hy hd
  · simpa only [neg_sub_neg,abs_sub_comm] using! hb x hx y hy hd

/-- Negation preserves the exact full Hölder norm
(BB Def 2.13 and Prop 2.15, pp. 81–82). -/
theorem holderENorm_neg (f : (Fin n → ℝ) → ℝ) :
    holderENorm d α V (fun x => -f x) = holderENorm d α V f := by
  simp only [holderENorm,abs_neg,holderSeminorm_neg]

/-- The triangle inequality for finite Hölder norms
(BB Prop 2.15, p. 82; elementary norm assembly). -/
theorem holderENorm_add_le (hα : 0 < α)
    (hsep : ∀ x ∈ V, ∀ y ∈ V,d x y = 0 → x = y)
    (f g : (Fin n → ℝ) → ℝ)
    (hf : holderENorm d α V f < ⊤) (hg : holderENorm d α V g < ⊤) :
    holderENorm d α V (fun x => f x+g x) ≤ holderENorm d α V f+holderENorm d α V g := by
  have hs : holderSeminorm d α V (fun x => f x+g x) ≤
      holderSeminorm d α V f+holderSeminorm d α V g := by
    apply holderSeminorm_le_of_bound
    · exact ENNReal.add_lt_top.mpr
        ⟨lt_of_le_of_lt le_add_self hf,lt_of_le_of_lt le_add_self hg⟩
    · intro x hx y hy hd
      have hr : |(f x+g x)-(f y+g y)| ≤ |f x-f y|+|g x-g y| := by
        calc
          _ = |(f x-f y)+(g x-g y)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      calc
        _ ≤ ENNReal.ofReal (|f x-f y|+|g x-g y|) := ENNReal.ofReal_le_ofReal hr
        _ = ENNReal.ofReal |f x-f y|+ENNReal.ofReal |g x-g y| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
        _ ≤ holderSeminorm d α V f*(d x y)^α+holderSeminorm d α V g*(d x y)^α :=
          add_le_add (holderSeminorm_increment_le d α V f hα hsep hx hy hd)
            (holderSeminorm_increment_le d α V g hα hsep hx hy hd)
        _ = _ := by rw [add_mul]
  have hn : (⨆ x : V,ENNReal.ofReal |f x.val+g x.val|) ≤
      (⨆ x : V,ENNReal.ofReal |f x.val|)+(⨆ x : V,ENNReal.ofReal |g x.val|) := by
    apply iSup_le
    intro x
    apply (ENNReal.ofReal_le_ofReal (abs_add_le _ _)).trans
    rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact add_le_add (le_iSup (fun z : V => ENNReal.ofReal |f z.val|) x)
      (le_iSup (fun z : V => ENNReal.ofReal |g z.val|) x)
  exact (add_le_add hn hs).trans_eq (by unfold holderENorm; ring)

/-- The difference norm is bounded by the sum of the two
finite norms (BB Prop 2.15, p. 82). -/
theorem holderENorm_sub_le (hα : 0 < α)
    (hsep : ∀ x ∈ V, ∀ y ∈ V,d x y = 0 → x = y)
    (f g : (Fin n → ℝ) → ℝ)
    (hf : holderENorm d α V f < ⊤) (hg : holderENorm d α V g < ⊤) :
    holderENorm d α V (fun x => f x-g x) ≤ holderENorm d α V f+holderENorm d α V g := by
  have H := holderENorm_add_le d α V hα hsep f (fun x => -g x) hf
    (by simpa only [holderENorm_neg] using hg)
  simpa only [sub_eq_add_neg,holderENorm_neg] using! H

end RothschildStein.S

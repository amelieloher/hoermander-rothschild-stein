-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderArithmetic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.S
variable {n : ℕ} {A : Type*}
variable (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (α : ℝ)
variable (V : Set (Fin n → ℝ))

/-- The zero function has zero Hölder norm
(BB Def 2.13, p. 81; finite Leibniz assembly). -/
theorem holderENorm_zero_function : holderENorm d α V (fun _ => 0) = 0 := by
  have hs : holderSeminorm d α V (fun _ => 0) = 0 := by
    apply le_antisymm
    · apply holderSeminorm_le_of_bound
      · exact ENNReal.zero_lt_top
      · intro x hx y hy hd
        simp only [sub_self,abs_zero,ENNReal.ofReal_zero,zero_mul,le_refl]
    · exact zero_le
  simp [holderENorm,hs]

/-- Finite lists of finite Hölder data have a finite-norm
sum (BB p. 84; finite Leibniz assembly). -/
theorem holderENorm_listSum_lt_top (hα : 0 < α)
    (hsep : ∀ x ∈ V,∀ y ∈ V,d x y = 0 → x = y)
    (items : List A) (F : A → (Fin n → ℝ) → ℝ)
    (h : ∀ a ∈ items,holderENorm d α V (F a) < ⊤) :
    holderENorm d α V (fun x => (items.map (fun a => F a x)).sum) < ⊤ := by
  induction items with
  | nil => simpa only [List.map_nil,List.sum_nil,holderENorm_zero_function] using ENNReal.zero_lt_top
  | cons a items ih =>
    have hh := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    simp only [List.map_cons,List.sum_cons]
    exact lt_of_le_of_lt (holderENorm_add_le d α V hα hsep _ _ hh ht)
      (ENNReal.add_lt_top.mpr ⟨hh,ht⟩)

/-- The Hölder norm of a finite list sum is at most
the sum of its norms (BB p. 84; Leibniz triangle inequality). -/
theorem holderENorm_listSum_le (hα : 0 < α)
    (hsep : ∀ x ∈ V,∀ y ∈ V,d x y = 0 → x = y)
    (items : List A) (F : A → (Fin n → ℝ) → ℝ)
    (h : ∀ a ∈ items,holderENorm d α V (F a) < ⊤) :
    holderENorm d α V (fun x => (items.map (fun a => F a x)).sum) ≤
      (items.map (fun a => holderENorm d α V (F a))).sum := by
  induction items with
  | nil => simp only [List.map_nil,List.sum_nil,holderENorm_zero_function,le_refl]
  | cons a items ih =>
    have hh := h a List.mem_cons_self
    have htail : ∀ b ∈ items,holderENorm d α V (F b) < ⊤ :=
      fun b hb => h b (List.mem_cons_of_mem a hb)
    simp only [List.map_cons,List.sum_cons]
    exact (holderENorm_add_le d α V hα hsep _ _ hh
      (holderENorm_listSum_lt_top d α V hα hsep items F htail)).trans
      (add_le_add le_rfl (ih htail))

end RothschildStein.S

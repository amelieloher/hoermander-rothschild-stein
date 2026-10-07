-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.holderENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.S
variable {n : ℕ}
variable (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
variable (α : ℝ) (V : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)

/-- Any finite increment bound bounds the seminorm
(BB Def 2.13, p. 81). Infinite-distance pairs are excluded exactly
as in the definition. -/
theorem holderSeminorm_le_of_bound (C : ℝ≥0∞) (hC : C < ⊤)
    (h : ∀ x ∈ V, ∀ y ∈ V, d x y < ⊤ →
      ENNReal.ofReal |f x-f y| ≤ C*(d x y)^α) :
    holderSeminorm d α V f ≤ C := sInf_le ⟨hC,h⟩

/-- The seminorm itself controls every finite-distance
increment when the distance separates points and the exponent is positive
(BB Def 2.13, p. 81; infimum attainment). -/
theorem holderSeminorm_increment_le (hα : 0 < α)
    (hsep : ∀ x ∈ V, ∀ y ∈ V, d x y = 0 → x = y)
    {x y : Fin n → ℝ} (hx : x ∈ V) (hy : y ∈ V) (hxy : d x y < ⊤) :
    ENNReal.ofReal |f x-f y| ≤ holderSeminorm d α V f*(d x y)^α := by
  by_cases he : x = y
  · subst y
    simp only [sub_self,abs_zero,ENNReal.ofReal_zero,zero_le]
  have hz : (d x y)^α ≠ 0 := by
    exact fun h => he (hsep x hx y hy ((ENNReal.rpow_eq_zero_iff_of_pos hα).mp h))
  have ht : (d x y)^α ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hα.le hxy.ne
  rw [← ENNReal.div_le_iff hz ht]
  apply le_sInf
  intro C hC
  rw [ENNReal.div_le_iff hz ht]
  exact hC.2 x hx y hy hxy

/-- Restriction decreases the seminorm while retaining
one fixed ambient distance (BB Prop 2.18, p. 84). -/
theorem holderSeminorm_mono {U : Set (Fin n → ℝ)} (hU : U ⊆ V) :
    holderSeminorm d α U f ≤ holderSeminorm d α V f := by
  apply sInf_le_sInf
  intro C hC
  exact ⟨hC.1,fun x hx y hy hxy => hC.2 x (hU hx) y (hU hy) hxy⟩

/-- Restriction decreases the exact full Hölder norm
(BB Prop 2.18, p. 84). -/
theorem holderENorm_mono {U : Set (Fin n → ℝ)} (hU : U ⊆ V) :
    holderENorm d α U f ≤ holderENorm d α V f := by
  apply add_le_add ?_ (holderSeminorm_mono d α V f hU)
  apply iSup_le
  intro x
  exact le_iSup_of_le ⟨x.val,hU x.property⟩ le_rfl

/-- The full norm bounds each pointwise value
(BB Def 2.13, p. 81). -/
theorem enorm_le_holderENorm {x : Fin n → ℝ} (hx : x ∈ V) :
    ENNReal.ofReal |f x| ≤ holderENorm d α V f :=
  (show ENNReal.ofReal |f x| ≤ ⨆ z : V, ENNReal.ofReal |f z.val| from
    le_iSup_of_le ⟨x,hx⟩ le_rfl).trans le_self_add

/-- Hölder seminorms depend only on pointwise values on the
specified set (BB Def 2.13, p. 81). -/
theorem holderSeminorm_congr {g : (Fin n → ℝ) → ℝ} (h : EqOn f g V) :
    holderSeminorm d α V f = holderSeminorm d α V g := by
  unfold holderSeminorm
  congr 1
  ext C
  constructor <;> rintro ⟨hC,hb⟩
  · exact ⟨hC,fun x hx y hy hd => by rw [← h hx,← h hy]; exact hb x hx y hy hd⟩
  · exact ⟨hC,fun x hx y hy hd => by rw [h hx,h hy]; exact hb x hx y hy hd⟩

/-- The full Hölder norm depends only on pointwise
values on its domain (BB Def 2.13, p. 81). -/
theorem holderENorm_congr {g : (Fin n → ℝ) → ℝ} (h : EqOn f g V) :
    holderENorm d α V f = holderENorm d α V g := by
  unfold holderENorm
  rw [holderSeminorm_congr d α V f h]
  congr 1
  apply iSup_congr
  intro x
  rw [h x.property]

end RothschildStein.S

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.PolynomialBCH
public import RothschildStein.G3.HomogeneousBasis
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- BCH transported through a linear coordinate identification
(BB Remark 10.51, p. 528). -/
def coordinateProduct {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u v : Fin M → ℝ) : Fin M → ℝ :=
  e.symm ⟨finiteBCH (e u).val (e v).val,
    finiteLieSpan_bch_mem (e u).property (e v).property⟩

/-- Coordinate identification preserves the concrete BCH product
(BB p. 528). -/
theorem coordinateProduct_map {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u v : Fin M → ℝ) :
    (e (coordinateProduct e u v)).val = finiteBCH (e u).val (e v).val := by
  exact congrArg Subtype.val (e.apply_symm_apply _)

/-- Associativity in model coordinates (BB p. 529). -/
theorem coordinateProduct_assoc {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u v w : Fin M → ℝ) :
    coordinateProduct e (coordinateProduct e u v) w =
      coordinateProduct e u (coordinateProduct e v w) := by
  apply e.injective
  apply Subtype.ext
  simp only [coordinateProduct_map]
  exact finiteBCH_assoc (formalSpan_positive_order (e u).val (e u).property)
    (formalSpan_positive_order (e v).val (e v).property)
    (formalSpan_positive_order (e w).val (e w).property)

/-- Left identity in model coordinates (BB p. 529). -/
@[simp] theorem coordinateProduct_zero_left {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u : Fin M → ℝ) : coordinateProduct e 0 u = u := by
  apply e.injective
  apply Subtype.ext
  rw [coordinateProduct_map, map_zero]
  exact finiteBCH_zero_left (formalSpan_positive_order (e u).val (e u).property)

/-- Right identity in model coordinates (BB p. 529). -/
@[simp] theorem coordinateProduct_zero_right {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u : Fin M → ℝ) : coordinateProduct e u 0 = u := by
  apply e.injective
  apply Subtype.ext
  rw [coordinateProduct_map, map_zero]
  exact finiteBCH_zero_right (formalSpan_positive_order (e u).val (e u).property)

/-- Left inverse in model coordinates (BB p. 529). -/
@[simp] theorem coordinateProduct_neg_left {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u : Fin M → ℝ) : coordinateProduct e (-u) u = 0 := by
  apply e.injective
  apply Subtype.ext
  rw [coordinateProduct_map, map_neg, map_zero]
  exact finiteBCH_neg_left (formalSpan_positive_order (e u).val (e u).property)

/-- Right inverse in model coordinates (BB p. 529). -/
@[simp] theorem coordinateProduct_neg_right {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u : Fin M → ℝ) : coordinateProduct e u (-u) = 0 := by
  apply e.injective
  apply Subtype.ext
  rw [coordinateProduct_map, map_neg, map_zero]
  exact finiteBCH_neg_right (formalSpan_positive_order (e u).val (e u).property)
end RothschildStein.G3

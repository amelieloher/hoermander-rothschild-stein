-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BCHLieClosure
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- BCH product on the concrete finite weighted free Lie carrier
(BB Proposition 10.52, pp. 528–529). -/
def modelProduct {a s : ℕ} {p : Fin a → ℕ+}
    (f g : coefficientLieAlgebra a s p) : coefficientLieAlgebra a s p :=
  ⟨finiteBCH f.val g.val, finiteLieSpan_bch_mem f.property g.property⟩

/-- The concrete BCH product is associative (BB p. 529). -/
theorem modelProduct_assoc {a s : ℕ} {p : Fin a → ℕ+}
    (f g h : coefficientLieAlgebra a s p) :
    modelProduct (modelProduct f g) h = modelProduct f (modelProduct g h) := by
  apply Subtype.ext
  exact finiteBCH_assoc (formalSpan_positive_order f.val f.property)
    (formalSpan_positive_order g.val g.property) (formalSpan_positive_order h.val h.property)

/-- Zero is a left identity (BB p. 529). -/
@[simp] theorem modelProduct_zero_left {a s : ℕ} {p : Fin a → ℕ+}
    (f : coefficientLieAlgebra a s p) : modelProduct 0 f = f := by
  apply Subtype.ext
  exact finiteBCH_zero_left (formalSpan_positive_order f.val f.property)

/-- Zero is a right identity (BB p. 529). -/
@[simp] theorem modelProduct_zero_right {a s : ℕ} {p : Fin a → ℕ+}
    (f : coefficientLieAlgebra a s p) : modelProduct f 0 = f := by
  apply Subtype.ext
  exact finiteBCH_zero_right (formalSpan_positive_order f.val f.property)

/-- Additive negation is a left inverse (BB p. 529). -/
@[simp] theorem modelProduct_neg_left {a s : ℕ} {p : Fin a → ℕ+}
    (f : coefficientLieAlgebra a s p) : modelProduct (-f) f = 0 := by
  apply Subtype.ext
  exact finiteBCH_neg_left (formalSpan_positive_order f.val f.property)

/-- Additive negation is a right inverse (BB p. 529). -/
@[simp] theorem modelProduct_neg_right {a s : ℕ} {p : Fin a → ℕ+}
    (f : coefficientLieAlgebra a s p) : modelProduct f (-f) = 0 := by
  apply Subtype.ext
  exact finiteBCH_neg_right (formalSpan_positive_order f.val f.property)

end RothschildStein.G3

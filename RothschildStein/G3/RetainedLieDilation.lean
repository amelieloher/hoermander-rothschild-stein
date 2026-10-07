-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RetainedLieListProducts
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

/-- Weighted dilation exposed on the formal-span carrier used by actual lists. -/
def retainedLieDilation {a s : ℕ} {p : Fin a → ℕ+} (t : ℝ)
    (f : formalSpan a s p) : formalSpan a s p := modelDilation t f

theorem retainedLieDilation_product {a s : ℕ} {p : Fin a → ℕ+} (t : ℝ)
    (f g : formalSpan a s p) : retainedLieDilation t (retainedLieProduct f g) =
      retainedLieProduct (retainedLieDilation t f) (retainedLieDilation t g) :=
  modelDilation_product t f g

@[simp] theorem retainedLieDilation_zero {a s : ℕ} {p : Fin a → ℕ+} (t : ℝ) :
    retainedLieDilation (a := a) (s := s) (p := p) t 0 = 0 := by
  apply Subtype.ext
  exact (dilationLinearMap t).map_zero

theorem retainedLieDilation_neg {a s : ℕ} {p : Fin a → ℕ+} (t : ℝ)
    (f : formalSpan a s p) : retainedLieDilation t (-f) = -(retainedLieDilation t f) := by
  apply Subtype.ext
  exact (dilationLinearMap t).map_neg f.val

theorem retainedLieListProduct_dilated {a s : ℕ} {p : Fin a → ℕ+} (t : ℝ)
    (fs : List (formalSpan a s p)) :
    retainedLieListProduct (fs.map (retainedLieDilation t)) =
      retainedLieDilation t (retainedLieListProduct fs) := by
  induction fs with
  | nil => simp only [List.map_nil,retainedLieListProduct,List.foldr_nil,retainedLieDilation_zero]
  | cons f fs ih =>
    simp only [List.map_cons,retainedLieListProduct,List.foldr_cons] at *
    rw [ih,retainedLieDilation_product]
end RothschildStein.G3

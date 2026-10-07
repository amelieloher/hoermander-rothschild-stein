-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.NestedResidualProducts
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1
open G3

/-- A tuple of singleton commutators is exactly the original associative word. -/
theorem nestedResidualProduct_letters {a : ℕ} (I : List (Fin a)) :
    nestedResidualProduct (I.map Nested.letter) = MonoidAlgebra.single (FreeMonoid.ofList I) 1 := by
  induction I with
  | nil => simp [nestedResidualProduct,← MonoidAlgebra.one_def]
  | cons i I ih =>
    change MonoidAlgebra.single (FreeMonoid.of i) 1 * nestedResidualProduct (I.map Nested.letter) = _
    rw [ih,MonoidAlgebra.single_mul_single,FreeMonoid.ofList_cons,one_mul]

/-- Primitive singleton factors retain exactly the word weight `wordWeight`. -/
theorem nestedResidualWeight_letters {a : ℕ} (p : Fin a → ℕ+) (I : List (Fin a)) :
    nestedResidualWeight p (I.map Nested.letter) = wordWeight p I := by
  simp [nestedResidualWeight,List.map_map,Function.comp_def,Nested.letters,wordWeight]
end RothschildStein.L1

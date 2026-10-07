-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TaylorWordMonomial
public import Mathlib.Algebra.BigOperators.Ring.List

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.P1

variable {N : ℕ}

/-- Prepending a coordinate distributes through the finite expansion. -/
theorem taylor_prepend_flatMap_sum {A : Type*}
    (js : List (Fin N)) (l : Fin N → List (List (Fin N) × A))
    (e : A → ℝ) (u : Fin N → ℝ) :
    (((js.flatMap (fun j => (l j).map (fun a => (j :: a.1, a.2)))).map
      (fun a => taylorWordMonomial a.1 u * e a.2)).sum) =
      (js.map (fun j => u j * ((l j).map
        (fun a => taylorWordMonomial a.1 u * e a.2)).sum)).sum := by
  induction js with
  | nil => simp only [List.flatMap_nil, List.map_nil, List.sum_nil]
  | cons j js ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, List.map_map, Function.comp_def, taylorWordMonomial_cons, mul_assoc,
      List.sum_map_mul_left, ih]

end RothschildStein.P1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.NestedTupleResiduals
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.L1
open G3

/-- Total tuple weight is the finite sum of factor weights. -/
theorem nestedResidualWeight_ofFn {a r : ℕ} (p : Fin a → ℕ+) (q : Fin r → Nested (Fin a)) :
    nestedResidualWeight p (List.ofFn q) = ∑ i, wordWeight p (q i).letters := by
  simp [nestedResidualWeight,List.map_ofFn,List.sum_ofFn]

/-- Each retained tuple factor fits whenever the total weight fits. -/
theorem nested_tuple_factor_weight_le {a r s : ℕ} (p : Fin a → ℕ+)
    (q : Fin r → Nested (Fin a)) (hw : nestedResidualWeight p (List.ofFn q) ≤ s) (i : Fin r) :
    wordWeight p (q i).letters ≤ s := by
  rw [nestedResidualWeight_ofFn] at hw
  exact (Finset.single_le_sum (fun j _ => Nat.zero_le (wordWeight p (q j).letters))
    (Finset.mem_univ i)).trans hw
end RothschildStein.L1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.BoxVolume
public import RothschildStein.G4.WeightedBoxes

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace RothschildStein.G4

/-- Exact Lebesgue volume of the shared weighted coefficient box
(BB Theorems 9.1/9.12, pp. 400, 405). -/
theorem volume_weightedBox {n : ℕ} (w : Fin n → ℕ+) {r : ℝ} (hr : 0 ≤ r) :
    volume (weightedBox w r) = ENNReal.ofReal (2 ^ n * r ^ (∑ i, (w i : ℕ))) := by
  have heq : weightedBox w r = Set.pi Set.univ
      (fun i => Set.Ioo (-(r ^ (w i : ℕ))) (r ^ (w i : ℕ))) := by
    ext a
    simp only [weightedBox, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const,
      Set.mem_Ioo, abs_lt]
  rw [heq]
  exact volume_weighted_coordinate_box (fun i => (w i : ℕ)) hr

end RothschildStein.G4

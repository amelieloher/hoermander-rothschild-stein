-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiniteHadamardExpansion

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.P1

/-- Positive coordinate weights dominate ordinary
word length. -/
theorem taylorWord_length_le_weight {N : ℕ} (G : HomogeneousGroup N) (J : List (Fin N)) :
    J.length ≤ (J.map G.weight).sum := by
  induction J with
  | nil => simp only [List.length_nil, List.map_nil, List.sum_nil, le_refl]
  | cons j J ih =>
    have hj := G.weight_pos j
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

end RothschildStein.P1

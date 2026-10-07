-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.FreeAt
public import RothschildStein.G3.Homogeneity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.L1

/-- Universal relations are preserved by graded scaling
of their coefficients (BB (10.51)–(10.54), pp. 524–526). -/
theorem formalRelation_weightedScale {a s : ℕ} {w : Fin a → ℕ+}
    (c : BoundedWord a s w → ℝ) (hc : FormalRelation c) (t : ℝ) :
    FormalRelation (fun I => t ^ wordWeight w (boundedWordList I) * c I) := by
  have hcoef := (G3.formalRelation_iff_coefficients c).mp hc
  apply (G3.formalRelation_iff_coefficients _).mpr
  intro J
  calc
    (∑ I, (t ^ wordWeight w (boundedWordList I) * c I) *
      formalBracket (boundedWordList I) (boundedWordList J)) =
        t ^ wordWeight w (boundedWordList J) *
          ∑ I, c I * formalBracket (boundedWordList I) (boundedWordList J) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro I _
            by_cases hweight : wordWeight w (boundedWordList J) = wordWeight w (boundedWordList I)
            · rw [hweight]
              ring
            · have hz := G3.formalBracket_homogeneous w (boundedWordList I) (boundedWordList J) hweight
              simp only [hz, mul_zero]
    _ = 0 := by rw [hcoef J, mul_zero]

/-- At an actual free point, every relation among bounded word
values is preserved by graded scaling (BB pp. 514–516, Proposition 10.35). -/
theorem weighted_relation_of_FreeAt {a n s : ℕ} {w : Fin a → ℕ+}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) {x : Fin n → ℝ}
    (hFree : FreeAt w s X x) (c : BoundedWord a s w → ℝ)
    (hc : (∑ I, c I • wordBracket X (boundedWordList I) x) = 0) (t : ℝ) :
    (∑ I, (t ^ wordWeight w (boundedWordList I) * c I) •
      wordBracket X (boundedWordList I) x) = 0 :=
  (hFree _).mpr (formalRelation_weightedScale c ((hFree c).mp hc) t)

end RothschildStein.L1

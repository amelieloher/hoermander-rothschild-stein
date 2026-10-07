-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompactWordLp
public import RothschildStein.H3.OperatorWordSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal BigOperators

/-- The drift operator of an actual compact smooth test is in every
Lp space; no integrability premise on its derivatives is required. -/
theorem memLp_sumSquaresWithDrift_compact {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (u : (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (huc : HasCompactSupport u) (p : ℝ≥0∞) :
    MemLp (sumSquaresWithDrift X u) p volume := by
  have hzero := memLp_wordDerivative_compact X hX [0] hu huc p
  have hsum := memLp_finsetSum (Finset.univ : Finset (Fin q))
    (fun i _ => memLp_wordDerivative_compact X hX [i.succ,i.succ] hu huc p)
  rw [sumSquaresWithDrift_eq_word_sum]
  apply hzero.add
  convert hsum using 1
  funext x
  simp only [Finset.sum_apply]

end RothschildStein.H3

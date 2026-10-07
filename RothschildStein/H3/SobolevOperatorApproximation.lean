-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SobolevWordApproximation
public import RothschildStein.H3.LpSumConvergence
public import RothschildStein.Definitions.driftWeight
public import RothschildStein.H3.OperatorWordSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

/-- The actual drift operator applied to the smooth Sobolev
approximants converges to the sum of its weak jets (BB p. 361). -/
theorem sumSquaresWithDrift_approximation_tendsto {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (u g₀ : (Fin n → ℝ) → ℝ)
    (g : Fin q → (Fin n → ℝ) → ℝ)
    (hg₀ : hasWeakWordDeriv X ⊤ [0] u g₀) (hgp₀ : MemLp g₀ p volume)
    (hg : ∀ i : Fin q, hasWeakWordDeriv X ⊤ [i.succ,i.succ] u (g i))
    (hgp : ∀ i, MemLp (g i) p volume)
    (A : SobolevWordApproximation driftWeight X p u) :
    Tendsto (fun k => eLpNorm
      (sumSquaresWithDrift X (A.functions k) - (g₀+∑ i, g i)) p volume) atTop (𝓝 0) := by
  have hi₀ : [(0 : Fin (q+1))] ∈ wordFamily driftWeight 2 := by
    simp [S.mem_wordFamily_iff,wordWeight,driftWeight]
  have hi : ∀ i : Fin q, [i.succ,i.succ] ∈ wordFamily driftWeight 2 := by
    intro i
    simp [S.mem_wordFamily_iff,wordWeight,driftWeight,Fin.succ_ne_zero]
  have hzero := A.word [0] hi₀ g₀ hg₀ hgp₀
  have hsum := lp_difference_finset_sum_tendsto volume hp Finset.univ g
    (fun i k => wordDerivative X [i.succ,i.succ] (A.functions k))
    (fun i _ => A.word [i.succ,i.succ] (hi i) (g i) (hg i) (hgp i))
  have hall := lp_difference_add_tendsto volume hp hzero hsum
  simpa only [sumSquaresWithDrift_eq_word_sum] using hall

end RothschildStein.H3

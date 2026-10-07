-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.OperatorAlgebra
public import RothschildStein.H1.ReversedOperator
public import RothschildStein.S.Transposes

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The transpose is additive on smooth functions,
including the cutoff partition used in the local pairing (BB p. 265). -/
theorem StandingHypotheses.transpose_add (H : StandingHypotheses G q)
    {f g : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Fin N → ℝ) :
    sumSquaresWithDriftTranspose H.fields (f + g) x =
      sumSquaresWithDriftTranspose H.fields f x + sumSquaresWithDriftTranspose H.fields g x := by
  have hfg : ContDiff ℝ (⊤ : ℕ∞) (f + g) := hf.add hg
  rw [← H.reverseDrift_operator G (f + g) hfg x,
    ← H.reverseDrift_operator G f hf x, ← H.reverseDrift_operator G g hg x]
  exact sumSquares_add_at (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt
    (fun i => ((H.reverseDrift G).fields_smooth G i.succ).differentiable (by simp) |>.differentiableAt)

/-- A transpose cannot enlarge support, including before the
smoothness of the paired kernel has been established (BB p. 265). -/
theorem tsupport_sumSquaresTranspose_subset
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (f : (Fin N → ℝ) → ℝ) :
    tsupport (sumSquaresWithDriftTranspose X f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hxf
  have hd (i : Fin (q + 1)) : fieldTranspose (X i) f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hxf (S.tsupport_fieldTranspose_subset (X i) f h))
  have hdd (i : Fin (q + 1)) : fieldTranspose (X i) (fieldTranspose (X i) f) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hxf
      ((S.tsupport_fieldTranspose_subset (X i) _).trans
        (S.tsupport_fieldTranspose_subset (X i) f) h))
  exact hx (by simp only [sumSquaresWithDriftTranspose, hd, hdd, Finset.sum_const_zero, add_zero])

end RothschildStein.H1

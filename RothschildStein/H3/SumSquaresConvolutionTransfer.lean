-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FarKernelTransfer
public import RothschildStein.Definitions.sumSquaresWithDrift

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace RothschildStein.H3
open G2

/-- far part. The full actual drift sum-of-squares transfers
from a compact smooth input to right fields on the smooth exterior kernel.
All finite integral interchanges have absolute convergence proved from
compact support (BB Proposition 3.47(c), applied on p. 383). -/
theorem sumSquaresWithDrift_left_right_convolution_transfer {N q : ℕ}
    (G : HomogeneousGroup N) (v : Fin (q + 1) → (Fin N → ℝ))
    {u F : (Fin N → ℝ) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hsu : HasCompactSupport u) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Fin N → ℝ) :
    groupConvolution G (sumSquaresWithDrift (fun i => leftField G (v i)) u) F x =
      groupConvolution G u (sumSquaresWithDrift (fun i => rightField G (v i)) F) x := by
  let Yl := fun i => leftField G (v i)
  let Yr := fun i => rightField G (v i)
  have hls (I : List (Fin (q + 1))) : ContDiff ℝ (⊤ : ℕ∞) (wordDerivative Yl I u) :=
    contDiffOn_univ.mp (S.contDiffOn_wordDerivative ⊤ Yl
      (fun i => (contDiff_leftField G (v i)).contDiffOn) I u hu.contDiffOn)
  have hrc (I : List (Fin (q + 1))) : Continuous (wordDerivative Yr I F) :=
    (contDiffOn_univ.mp (S.contDiffOn_wordDerivative ⊤ Yr
      (fun i => (contDiff_rightField G (v i)).contDiffOn) I F hF.contDiffOn)).continuous
  have hlc (I : List (Fin (q + 1))) : HasCompactSupport (wordDerivative Yl I u) :=
    hsu.of_isClosed_subset (isClosed_tsupport _) (S.tsupport_wordDerivative_subset Yl I u)
  have hlex (I : List (Fin (q + 1))) :=
    groupConvolution_exists_compact_continuous_kernel G (hls I).continuous (hlc I) hF.continuous x
  have hrex (I : List (Fin (q + 1))) :=
    groupConvolution_exists_compact_continuous_kernel G hu.continuous hsu (hrc I) x
  have hl0 : Integrable (fun y => fieldDerivative (Yl 0) u y * F (G.mul (G.inv y) x)) volume :=
    hlex [0]
  have hl2 (i : Fin q) : Integrable (fun y =>
      fieldDerivative (Yl i.succ) (fieldDerivative (Yl i.succ) u) y * F (G.mul (G.inv y) x)) volume :=
    hlex [i.succ, i.succ]
  have hr0 : Integrable (fun y => u y * fieldDerivative (Yr 0) F (G.mul (G.inv y) x)) volume :=
    hrex [0]
  have hr2 (i : Fin q) : Integrable (fun y => u y *
      fieldDerivative (Yr i.succ) (fieldDerivative (Yr i.succ) F) (G.mul (G.inv y) x)) volume :=
    hrex [i.succ, i.succ]
  have hleft : groupConvolution G (sumSquaresWithDrift Yl u) F x =
      groupConvolution G (fieldDerivative (Yl 0) u) F x +
        ∑ i : Fin q, groupConvolution G
          (fieldDerivative (Yl i.succ) (fieldDerivative (Yl i.succ) u)) F x := by
    simp only [groupConvolution_eq_integral, sumSquaresWithDrift, add_mul, Finset.sum_mul]
    rw [integral_add hl0 (integrable_finsetSum Finset.univ (fun i _ => hl2 i)),
      integral_finsetSum Finset.univ (fun i _ => hl2 i)]
  have hright : groupConvolution G u (sumSquaresWithDrift Yr F) x =
      groupConvolution G u (fieldDerivative (Yr 0) F) x +
        ∑ i : Fin q, groupConvolution G u
          (fieldDerivative (Yr i.succ) (fieldDerivative (Yr i.succ) F)) x := by
    simp only [groupConvolution_eq_integral, sumSquaresWithDrift, mul_add, Finset.mul_sum]
    rw [integral_add hr0 (integrable_finsetSum Finset.univ (fun i _ => hr2 i)),
      integral_finsetSum Finset.univ (fun i _ => hr2 i)]
  rw [hleft, hright]
  congr 1
  · exact groupConvolution_leftField_transfer G (v 0) hu hsu hF x
  · apply Finset.sum_congr rfl
    intro i _
    exact groupConvolution_leftField_square_transfer G (v i.succ) hu hsu hF x

/-- The transfer identity for the prescribed shared invariant
frame, with right partners determined by its actual identity values. -/
theorem sumSquaresWithDrift_invariant_convolution_transfer {N q : ℕ}
    (G : HomogeneousGroup N)
    (Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ∀ i, IsLeftInvariantField G (Y i))
    {u F : (Fin N → ℝ) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hsu : HasCompactSupport u) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Fin N → ℝ) :
    groupConvolution G (sumSquaresWithDrift Y u) F x =
      groupConvolution G u (sumSquaresWithDrift (fun i => rightField G (Y i 0)) F) x := by
  have he : Y = (fun i => leftField G (Y i 0)) := funext (fun i => (hY i).eq_leftField G)
  have hh := sumSquaresWithDrift_left_right_convolution_transfer G (fun i => Y i 0) hu hsu hF x
  simpa only [← he] using hh

end RothschildStein.H3

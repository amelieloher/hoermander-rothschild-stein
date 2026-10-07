-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.Transpose

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.H1
open scoped BigOperators
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- A homogeneous field square has twice the field degree (BB p. 254). -/
theorem fieldSquare_homogeneous
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (a : ℝ) (ha : G2.IsHomogeneousField G V a) :
    G2.IsHomogeneousOperator G (fun f => fieldDerivative V (fieldDerivative V f)) (a + a) := by
  intro f hf t ht x
  have hop := (G2.isHomogeneousField_iff_operator G V a).mp ha
  have hdf := smooth_fieldDerivative V hV f hf
  have he : fieldDerivative V (f ∘ G.dilate t) =
      fun y => t ^ a * fieldDerivative V f (G.dilate t y) := funext (hop f hf t ht)
  change fieldDerivative V (fieldDerivative V (f ∘ G.dilate t)) x = _
  rw [he]
  have hd : DifferentiableAt ℝ (fieldDerivative V f ∘ G.dilate t) x :=
    ((hdf.comp (G2.contDiff_dilate G t)).differentiable (by simp)).differentiableAt
  have hc : fderiv ℝ (fun y => t ^ a * fieldDerivative V f (G.dilate t y)) x =
      t ^ a • fderiv ℝ (fieldDerivative V f ∘ G.dilate t) x := by
    convert (hd.hasFDerivAt.const_mul (t ^ a)).fderiv using 1
    congr 1
  change fderiv ℝ (fun y => t ^ a * fieldDerivative V f (G.dilate t y)) x (V x) = _
  rw [hc]
  change t ^ a * fieldDerivative V (fieldDerivative V f ∘ G.dilate t) x = _
  rw [hop _ hdf t ht x, Real.rpow_add ht]
  ring

/-- The sum-of-squares-with-drift operator has degree two (BB p. 254). -/
theorem StandingHypotheses.operator_homogeneous (H : StandingHypotheses G q) :
    G2.IsHomogeneousOperator G (sumSquaresWithDrift H.fields) 2 := by
  intro f hf t ht x
  have h0 : G2.IsHomogeneousOperator G (fieldDerivative (H.fields 0)) 2 :=
    (G2.isHomogeneousField_iff_operator G _ _).mp (by simpa using H.homogeneous 0)
  have hi : ∀ i : Fin q, G2.IsHomogeneousOperator G
      (fun f => fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields i.succ) f)) 2 := by
    intro i
    have hh : G2.IsHomogeneousField G (H.fields i.succ) 1 := by simpa using H.homogeneous i.succ
    convert fieldSquare_homogeneous G _ (H.fields_smooth G i.succ) 1 hh using 1
    norm_num
  unfold sumSquaresWithDrift
  rw [h0 f hf t ht x, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact hi i f hf t ht x

end RothschildStein.H1

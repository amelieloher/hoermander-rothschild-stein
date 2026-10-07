-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.TimedPrimitiveLieInputs
public import RothschildStein.G3.RetainedLieDilation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

theorem retainedLieDilation_singleton {a s : ℕ} {p : Fin a → ℕ+}
    (t : ℝ) (i : Fin a) : retainedLieDilation t (wordLieElement [i] : formalSpan a s p) =
      t^(p i : ℕ) • (wordLieElement [i] : formalSpan a s p) :=
  quasiExponentialLogAt_singleton t i

theorem timedPrimitiveLieInput_signed {a s : ℕ} {p : Fin a → ℕ+}
    (b : Fin a × Bool) (t : ℝ) :
    timedPrimitiveLieInput (s := s) (p := p) (b.1,signedPrimitiveTime p b t) =
      retainedLieDilation t (primitiveScheduleLieInput b) := by
  rcases b with ⟨i,b⟩
  cases b
  · change -(t^(p i : ℕ)) • (wordLieElement [i] : formalSpan a s p) =
      retainedLieDilation t (-(wordLieElement [i] : formalSpan a s p))
    rw [retainedLieDilation_neg,retainedLieDilation_singleton]
    apply Subtype.ext
    funext J
    change (-(t^(p i : ℕ)))*_ = -(t^(p i : ℕ)*_)
    ring
  · exact (retainedLieDilation_singleton t i).symm

/-- Root choices are fixed constants; their primitive Lie product is exact. -/
theorem rootTimedPrimitiveSchedule_retainedLieProduct {a s : ℕ} {p : Fin a → ℕ+}
    (A : ℝ × List (Fin a)) : retainedLieListProduct
      ((rootTimedPrimitiveSchedule p A).map (timedPrimitiveLieInput (s := s) (p := p))) =
      (signedQuasiCorrection A.1 A.2 : formalSpan a s p) := by
  let t := |A.1| ^ ((wordWeight p A.2 : ℝ)⁻¹)
  have hm : (rootTimedPrimitiveSchedule p A).map (timedPrimitiveLieInput (s := s) (p := p)) =
      ((signedCorrectionSchedule A).map primitiveScheduleLieInput).map (retainedLieDilation t) := by
    simp only [rootTimedPrimitiveSchedule,List.map_map]
    apply List.map_congr_left
    intro b _
    exact timedPrimitiveLieInput_signed b t
  rw [hm,retainedLieListProduct_dilated]
  by_cases hA : 0 ≤ A.1
  · simp only [signedCorrectionSchedule,ite_eq_left hA,commutatorSchedule_retainedLieListProduct]
    unfold signedQuasiCorrection
    rw [ite_eq_left hA]
    rfl
  · simp only [signedCorrectionSchedule,ite_eq_right hA,primitiveScheduleLieInput_inverse,
      retainedLieListProduct_inverse,commutatorSchedule_retainedLieListProduct]
    unfold signedQuasiCorrection
    rw [ite_eq_right hA]
    apply Subtype.ext
    exact (dilationLinearMap t).map_neg (quasiExponentialLog A.2).val
end RothschildStein.G3

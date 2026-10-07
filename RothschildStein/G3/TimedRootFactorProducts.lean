-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.TimedRootLieProducts
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

/-- The complete real primitive schedule has exactly the selected formal target. -/
theorem rootTimedFactorSchedule_retainedLieProduct {a s : ℕ} {p : Fin a → ℕ+}
    (AS : List (ℝ × List (Fin a))) : retainedLieListProduct
      ((rootTimedFactorSchedule p AS).map (timedPrimitiveLieInput (s := s) (p := p))) =
      (⟨signedWordProduct AS,signedWordProduct_mem AS⟩ : formalSpan a s p) := by
  induction AS with
  | nil => rfl
  | cons A AS ih =>
    have happ : rootTimedFactorSchedule p (A::AS) =
        rootTimedPrimitiveSchedule p A ++ rootTimedFactorSchedule p AS := rfl
    rw [happ,List.map_append,retainedLieListProduct_append]
    have hhead : retainedLieListProduct ((rootTimedPrimitiveSchedule p A).map
        (timedPrimitiveLieInput (s := s) (p := p))) =
        (⟨(signedQuasiCorrection A.1 A.2).val,(signedQuasiCorrection A.1 A.2).property⟩ : formalSpan a s p) :=
      rootTimedPrimitiveSchedule_retainedLieProduct A
    apply (congrArg₂ (retainedLieProduct (s := s) (p := p)) hhead ih).trans
    apply Subtype.ext
    rfl

@[simp] theorem timedPrimitiveLieInput_zero {a s : ℕ} {p : Fin a → ℕ+} (i : Fin a) :
    timedPrimitiveLieInput (s := s) (p := p) (i,0) = 0 := zero_smul ℝ _

@[simp] theorem retainedLieListProduct_replicate_zero {a s : ℕ} {p : Fin a → ℕ+} (n : ℕ) :
    retainedLieListProduct (List.replicate n (0 : formalSpan a s p)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,retainedLieListProduct,List.foldr_cons] at *
    rw [ih,retainedLieProduct_zero_left]

/-- Zero padding preserves the exact formal primitive product. -/
theorem paddedTimedSchedule_retainedLieProduct {a s : ℕ} {p : Fin a → ℕ+}
    (i : Fin a) (L : ℕ) (S : List (Fin a × ℝ)) :
    retainedLieListProduct ((padTimedPrimitiveSchedule i L S).map
      (timedPrimitiveLieInput (s := s) (p := p))) =
      retainedLieListProduct (S.map timedPrimitiveLieInput) := by
  simp only [padTimedPrimitiveSchedule,List.map_append,List.map_replicate,
    timedPrimitiveLieInput_zero,retainedLieListProduct_append,retainedLieListProduct_replicate_zero,
    retainedLieProduct_zero_right]
end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G3.MathlibBridgeCoefficients

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3
variable {a : ℕ}

/-- The associative free word is the ordered
product of its generators (BB p. 467). -/
def mathlibWord (I : List (Fin a)) : FreeAlgebra ℚ (Fin a) :=
  (I.map (FreeAlgebra.ι ℚ)).prod

/-- Word coefficients of the ordered free product
are the existing coefficient monomial (BB p. 467). -/
theorem mathlibCoefficients_word (I : List (Fin a)) :
    mathlibCoefficients a (mathlibWord I) = wordSeries I := by
  induction I with
  | nil => exact (mathlibCoefficients a).map_one
  | cons i I ih =>
    change mathlibCoefficients a (FreeAlgebra.ι ℚ i * mathlibWord I) = _
    rw [map_mul,mathlibCoefficients_generator,ih,wordSeries_cons]

/-- Ordered free words are the monoid-algebra
basis vectors under Mathlib's canonical equivalence (BB p. 467). -/
theorem mathlibWord_equiv (I : List (Fin a)) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid (mathlibWord I) =
      MonoidAlgebra.single (FreeMonoid.ofList I) (1 : ℚ) := by
  classical
  ext W
  simp only [MonoidAlgebra.coeff_single,Finsupp.single_apply]
  rw [@eq_comm _ (FreeMonoid.ofList I) W]
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid (mathlibWord I)).coeff W =
    if W = FreeMonoid.ofList I then 1 else 0
  have h := congrFun (mathlibCoefficients_word I) W.toList
  rw [mathlibCoefficients_apply,FreeMonoid.ofList_toList] at h
  change ((FreeAlgebra.equivMonoidAlgebraFreeMonoid (mathlibWord I)).coeff W : ℝ) =
    if W.toList = I then 1 else 0 at h
  by_cases he : W = FreeMonoid.ofList I
  · subst W
    rw [ite_eq_left rfl]
    apply Rat.cast_injective (α := ℝ)
    simpa using h
  · rw [ite_eq_right he]
    apply Rat.cast_injective (α := ℝ)
    have hne : W.toList ≠ I := by
      intro heq
      apply he
      rw [← heq,FreeMonoid.ofList_toList]
    simpa only [ite_eq_right hne,Rat.cast_zero] using h

/-- Every rational free polynomial is its finite
word-basis expansion (BB p. 467). -/
theorem mathlibWord_expansion (f : FreeAlgebra ℚ (Fin a)) :
    f = ∑ I ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid f).coeff.support,
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid f).coeff I • mathlibWord I.toList := by
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  rw [map_sum]
  simp_rw [map_smul,mathlibWord_equiv,FreeMonoid.ofList_toList,
    MonoidAlgebra.smul_single,smul_eq_mul,mul_one]
  exact (MonoidAlgebra.sum_coeff_single _).symm

/-- Word-length grading transfers the homogeneous
rational generator span into the coefficient grading (BB p. 467). -/
theorem mathlibCoefficients_homogeneous_of_generatorSpan_pow {n : ℕ}
    {f : FreeAlgebra ℚ (Fin a)}
    (hf : f ∈ Submodule.span ℚ (Set.range (FreeAlgebra.ι ℚ : Fin a → FreeAlgebra ℚ (Fin a))) ^ n) :
    Homogeneous (fun _ => 1) n (mathlibCoefficients a f) := by
  let M := Submodule.span ℚ (Set.range (FreeAlgebra.ι ℚ : Fin a → FreeAlgebra ℚ (Fin a)))
  have hM : ∀ g ∈ M,Homogeneous (fun _ => 1) 1 (mathlibCoefficients a g) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨i,rfl⟩ := hg
      rw [mathlibCoefficients_generator]
      exact homogeneous_letter _ i
    | zero => intro I _; rw [map_zero]; rfl
    | add f g _ _ hf hg =>
      intro I hI
      rw [map_add]
      change mathlibCoefficients a f I + mathlibCoefficients a g I = 0
      rw [hf I hI,hg I hI,add_zero]
    | smul r f _ hf => intro I hI; rw [map_smul]; change (r : ℝ)*_ = 0; rw [hf I hI,mul_zero]
  induction n generalizing f with
  | zero =>
    rw [Submodule.pow_zero,Submodule.one_eq_span] at hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain rfl := Set.mem_singleton_iff.mp hf
      intro I hI
      rw [map_one]
      change (if I = [] then (1 : ℝ) else 0) = 0
      exact ite_eq_right (fun h => hI (by subst I; rfl))
    | zero => intro I _; rw [map_zero]; rfl
    | add f g _ _ hf hg =>
      intro I hI
      rw [map_add]
      change mathlibCoefficients a f I + mathlibCoefficients a g I = 0
      rw [hf I hI,hg I hI,add_zero]
    | smul r f _ hf => intro I hI; rw [map_smul]; change (r : ℝ)*_ = 0; rw [hf I hI,mul_zero]
  | succ n ih =>
    rw [Submodule.pow_succ] at hf
    refine Submodule.mul_induction_on hf (fun f hf g hg => ?_) (fun f g hf hg => ?_)
    · rw [map_mul]
      exact homogeneous_convolution _ (ih hf) (hM g hg)
    · intro I hI
      rw [map_add]
      change mathlibCoefficients a f I + mathlibCoefficients a g I = 0
      rw [hf I hI,hg I hI,add_zero]

end RothschildStein.G3

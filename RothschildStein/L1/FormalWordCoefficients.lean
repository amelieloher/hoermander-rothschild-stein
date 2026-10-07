-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ModelFreedom
public import RothschildStein.G3.ModelBasisWords
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.L1
open G3

/-- The finite formal commutator combination map (BB (10.2), p. 486). -/
def formalWordCoefficientMap {a s : ℕ} {p : Fin a → ℕ+} :
    (BoundedWord a s p → ℝ) →ₗ[ℝ] formalSpan a s p where
  toFun c := ∑ I, c I • wordLieElement (boundedWordList I)
  map_add' c d := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r c := by
    simp only [Pi.smul_apply,smul_smul,Finset.smul_sum,RingHom.id_apply,smul_eq_mul]

theorem formalWordCoefficientMap_single {a s : ℕ} {p : Fin a → ℕ+}
    (I : BoundedWord a s p) :
    formalWordCoefficientMap (Pi.single I (1 : ℝ)) = wordLieElement (boundedWordList I) := by
  classical
  simp [formalWordCoefficientMap,Pi.single_apply]

/-- Universal relations are precisely the kernel of the formal combination map. -/
theorem formalWordCoefficientMap_eq_zero_iff {a s : ℕ} {p : Fin a → ℕ+}
    (c : BoundedWord a s p → ℝ) : formalWordCoefficientMap c = 0 ↔ FormalRelation c :=
  (formalRelation_iff_wordLieElement_sum_zero c).symm
end RothschildStein.L1

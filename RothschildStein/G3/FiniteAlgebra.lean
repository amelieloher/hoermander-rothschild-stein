-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.Truncation
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Associative algebra structure on a type synonym of the fixed carrier;
this avoids replacing its pointwise function multiplication (BB p. 525). -/
def FiniteWordAlgebra (a s : ℕ) (p : Fin a → ℕ+) := WordCoefficients a s p

instance finiteWordAddCommGroup {a s : ℕ} {p : Fin a → ℕ+} : AddCommGroup (FiniteWordAlgebra a s p) :=
  inferInstanceAs (AddCommGroup (WordCoefficients a s p))
instance finiteWordRealModule {a s : ℕ} {p : Fin a → ℕ+} : Module ℝ (FiniteWordAlgebra a s p) :=
  inferInstanceAs (Module ℝ (WordCoefficients a s p))
instance finiteWordMul {a s : ℕ} {p : Fin a → ℕ+} : Mul (FiniteWordAlgebra a s p) :=
  ⟨truncatedProduct⟩
instance finiteWordOne {a s : ℕ} {p : Fin a → ℕ+} : One (FiniteWordAlgebra a s p) :=
  ⟨truncatedUnit⟩

instance finiteWordRing {a s : ℕ} {p : Fin a → ℕ+} : Ring (FiniteWordAlgebra a s p) where
  __ := (inferInstance : AddCommGroup (FiniteWordAlgebra a s p))
  mul_assoc := truncatedProduct_assoc
  one_mul := truncatedProduct_unit_left
  mul_one := truncatedProduct_unit_right
  left_distrib := truncatedProduct_add_right
  right_distrib := truncatedProduct_add_left
  zero_mul f := by
    funext J
    change wordConvolution (extend 0) (extend f) _ = 0
    rw [extend_zero]
    simp [wordConvolution]
  mul_zero f := by
    funext J
    change wordConvolution (extend f) (extend 0) _ = 0
    rw [extend_zero]
    simp [wordConvolution]
  natCast := fun n => n • (1 : FiniteWordAlgebra a s p)
  natCast_zero := by simp
  natCast_succ n := by simp [add_smul]
  intCast := fun n => n • (1 : FiniteWordAlgebra a s p)
  intCast_ofNat n := natCast_zsmul _ _
  intCast_negSucc n := negSucc_zsmul _ _

instance finiteWordRealAlgebra {a s : ℕ} {p : Fin a → ℕ+} : Algebra ℝ (FiniteWordAlgebra a s p) :=
  Algebra.ofModule truncatedProduct_smul_left truncatedProduct_smul_right

end RothschildStein.G3

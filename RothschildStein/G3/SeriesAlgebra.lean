-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.Convolution
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Completion of the associative word algebra, represented coefficientwise
(BB pp. 467–469). The empty word is retained. -/
def CoefficientSeries (a : ℕ) := List (Fin a) → ℝ

instance seriesAddCommGroup {a : ℕ} : AddCommGroup (CoefficientSeries a) :=
  inferInstanceAs (AddCommGroup (List (Fin a) → ℝ))
instance seriesRealModule {a : ℕ} : Module ℝ (CoefficientSeries a) :=
  inferInstanceAs (Module ℝ (List (Fin a) → ℝ))
instance seriesMul {a : ℕ} : Mul (CoefficientSeries a) := ⟨wordConvolution⟩
instance seriesOne {a : ℕ} : One (CoefficientSeries a) := ⟨wordUnit⟩

instance seriesRing {a : ℕ} : Ring (CoefficientSeries a) where
  __ := (inferInstance : AddCommGroup (CoefficientSeries a))
  mul_assoc f g h := by funext J; exact convolution_assoc f g h J
  one_mul f := by funext J; exact convolution_unit_left f J
  mul_one f := by funext J; exact convolution_unit_right f J
  left_distrib f g h := by funext J; exact convolution_add_right f g h J
  right_distrib f g h := by funext J; exact convolution_add_left f g h J
  zero_mul f := by
    funext J
    change wordConvolution (fun _ => 0) f J = 0
    simp [wordConvolution]
  mul_zero f := by
    funext J
    change wordConvolution f (fun _ => 0) J = 0
    simp [wordConvolution]
  natCast := fun n => n • (1 : CoefficientSeries a)
  natCast_zero := by simp
  natCast_succ n := by simp [add_smul]
  intCast := fun n => n • (1 : CoefficientSeries a)
  intCast_ofNat n := natCast_zsmul _ _
  intCast_negSucc n := negSucc_zsmul _ _

instance seriesRealAlgebra {a : ℕ} : Algebra ℝ (CoefficientSeries a) :=
  Algebra.ofModule
    (fun r f g => by funext J; exact convolution_smul_left r f g J)
    (fun r f g => by funext J; exact convolution_smul_right r f g J)

/-- Coefficient access in the completed word algebra (BB p. 467). -/
def coefficient {a : ℕ} (f : CoefficientSeries a) (J : List (Fin a)) : ℝ := f J

/-- Multiplication in the completion is exactly fixed word convolution
(BB (9.73), p. 467). -/
@[simp] theorem coefficient_mul {a : ℕ} (f g : CoefficientSeries a) (J : List (Fin a)) :
    coefficient (f * g) J = wordConvolution f g J := rfl

/-- Scalar multiplication remains coefficientwise (BB p. 467). -/
@[simp] theorem coefficient_smul {a : ℕ} (r : ℝ) (f : CoefficientSeries a)
    (J : List (Fin a)) : coefficient (r • f) J = r * coefficient f J := rfl

/-- The constant coefficient is a real-algebra homomorphism
(BB pp. 467–468). -/
def constantCoefficient (a : ℕ) : CoefficientSeries a →ₐ[ℝ] ℝ where
  toFun f := coefficient f []
  map_one' := by
    change @wordUnit a [] = 1
    simp [wordUnit]
  map_mul' f g := convolution_nil f g
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    change r * wordUnit [] = r
    simp [wordUnit]

end RothschildStein.G3

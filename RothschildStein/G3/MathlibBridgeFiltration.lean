-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G3.MathlibBridgeWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G3
variable {a : ℕ}

/-- Mathlib's augmentation ideal in the rational
free associative algebra (BB pp. 467–468). -/
@[instance_reducible]
def mathlibAugmentation (a : ℕ) : Ideal (FreeAlgebra ℚ (Fin a)) :=
  RingHom.ker (FreeAlgebra.algebraMapInv : FreeAlgebra ℚ (Fin a) →ₐ[ℚ] ℚ)

/-- The augmentation kernel is two-sided
(BB p. 468). -/
instance mathlibAugmentation_isTwoSided (a : ℕ) : (mathlibAugmentation a).IsTwoSided := by
  unfold mathlibAugmentation
  infer_instance

/-- Augmentation is exactly the constant word
coefficient, transported to the real completion (BB p. 467). -/
theorem mathlibCoefficients_constant (f : FreeAlgebra ℚ (Fin a)) :
    mathlibCoefficients a f [] = ((FreeAlgebra.algebraMapInv f : ℚ) : ℝ) := by
  let L : FreeAlgebra ℚ (Fin a) →ₐ[ℚ] ℝ :=
    ((constantCoefficient a).restrictScalars ℚ).comp (mathlibCoefficients a)
  let R : FreeAlgebra ℚ (Fin a) →ₐ[ℚ] ℝ :=
    ((algebraMap ℚ ℝ).toRatAlgHom).comp FreeAlgebra.algebraMapInv
  have he : L = R := by
    ext i
    simp [L,R,constantCoefficient,mathlibCoefficients_generator,FreeAlgebra.algebraMapInv,
      letterSeries,coefficient]
  exact AlgHom.congr_fun he f

/-- The augmentation ideal is the positive-degree
part of the rational coefficient embedding (BB p. 468). -/
theorem mem_mathlibAugmentation_iff (f : FreeAlgebra ℚ (Fin a)) :
    f ∈ mathlibAugmentation a ↔ PositiveSeries (mathlibCoefficients a f) := by
  change FreeAlgebra.algebraMapInv f = 0 ↔ mathlibCoefficients a f [] = 0
  rw [mathlibCoefficients_constant]
  exact Rat.cast_eq_zero.symm

/-- Lower degree is a left ideal in the free
associative algebra (BB pp. 467–468). -/
def mathlibTailIdeal (a k : ℕ) : Ideal (FreeAlgebra ℚ (Fin a)) where
  carrier := {f | OrderAtLeast (fun _ => 1) k (mathlibCoefficients a f)}
  zero_mem' := by intro I _; rw [map_zero]; rfl
  add_mem' := by
    intro f g hf hg I hI
    rw [map_add]
    change mathlibCoefficients a f I + mathlibCoefficients a g I = 0
    rw [hf I hI,hg I hI,add_zero]
  smul_mem' := by
    intro r f hf
    change OrderAtLeast (fun _ => 1) k (mathlibCoefficients a (r*f))
    rw [map_mul]
    change OrderAtLeast (fun _ => 1) k
      (wordConvolution (mathlibCoefficients a r) (mathlibCoefficients a f))
    simpa only [Nat.zero_add] using orderAtLeast_convolution (fun _ => 1)
      (k := 0) (f := mathlibCoefficients a r)
      (fun I h => False.elim (Nat.not_lt_zero _ h)) hf

/-- Products of augmentation elements have no
coefficients below the number of factors (BB p. 468). -/
theorem mathlibAugmentation_pow_le_tail (k : ℕ) :
    mathlibAugmentation a ^ k ≤ mathlibTailIdeal a k := by
  induction k with
  | zero => intro f _ I hI; exact False.elim (Nat.not_lt_zero _ hI)
  | succ k ih =>
    rw [Ideal.IsTwoSided.pow_succ]
    apply Ideal.mul_le.mpr
    intro f hf g hg
    have hfp := (mem_mathlibAugmentation_iff f).mp hf
    have hf1 : OrderAtLeast (fun _ : Fin a => 1) 1 (mathlibCoefficients a f) := by
      intro I hI
      have hz : I = [] := by rw [ordinary_weight] at hI; exact List.length_eq_zero_iff.mp (by omega)
      subst I
      exact hfp
    have hp := orderAtLeast_convolution (fun _ => 1) hf1 (ih hg)
    change OrderAtLeast (fun _ => 1) (k+1) (mathlibCoefficients a (f*g))
    rw [map_mul]
    change OrderAtLeast (fun _ => 1) (k+1)
      (wordConvolution (mathlibCoefficients a f) (mathlibCoefficients a g))
    rw [Nat.add_comm k 1]
    exact hp

/-- A word belongs to the augmentation power
specified by its ordinary length (BB p. 468). -/
theorem mathlibWord_mem_augmentation_pow (I : List (Fin a)) :
    mathlibWord I ∈ mathlibAugmentation a ^ I.length := by
  induction I with
  | nil => rw [List.length_nil,Submodule.pow_zero,Ideal.one_eq_top]; exact Submodule.mem_top
  | cons i I ih =>
    change FreeAlgebra.ι ℚ i * mathlibWord I ∈ mathlibAugmentation a ^ (I.length+1)
    rw [Ideal.IsTwoSided.pow_succ]
    apply Ideal.mul_mem_mul ?_ ih
    change FreeAlgebra.algebraMapInv (FreeAlgebra.ι ℚ i) = 0
    simp [FreeAlgebra.algebraMapInv]

/-- The augmentation power is precisely the
span of words of length at least k (BB pp. 467–468). -/
theorem mathlibAugmentation_pow_eq_tail (k : ℕ) :
    mathlibAugmentation a ^ k = mathlibTailIdeal a k := by
  apply le_antisymm (mathlibAugmentation_pow_le_tail k)
  intro f hf
  rw [mathlibWord_expansion f]
  apply Submodule.sum_mem
  intro I hI
  have hlen : k ≤ I.toList.length := by
    by_contra hn
    have hz := hf I.toList (by rw [ordinary_weight]; omega)
    rw [mathlibCoefficients_apply,FreeMonoid.ofList_toList] at hz
    have hq : (FreeAlgebra.equivMonoidAlgebraFreeMonoid f).coeff I = 0 := Rat.cast_eq_zero.mp hz
    exact (Finsupp.mem_support_iff.mp hI) hq
  have hword := Ideal.pow_le_pow_right (I := mathlibAugmentation a) hlen
    (mathlibWord_mem_augmentation_pow I.toList)
  simpa only [Algebra.smul_def,smul_eq_mul] using (mathlibAugmentation a ^ k).smul_mem
    (algebraMap ℚ (FreeAlgebra ℚ (Fin a)) ((FreeAlgebra.equivMonoidAlgebraFreeMonoid f).coeff I)) hword

/-- The finite coefficient map has exactly the
fixed augmentation-power kernel (BB pp. 468–469). -/
theorem mathlibTruncation_ker (N : ℕ) :
    RingHom.ker (mathlibTruncation a N) = mathlibAugmentation a ^ (N+1) := by
  rw [mathlibAugmentation_pow_eq_tail]
  ext f
  constructor
  · intro hf I hI
    have hlen : I.length ≤ N := by rw [ordinary_weight] at hI; omega
    change mathlibTruncation a N f = 0 at hf
    have he := congrFun hf (boundedWord (fun _ => 1) I (by rw [ordinary_weight]; exact hlen))
    exact he
  · intro hf
    change mathlibTruncation a N f = 0
    funext I
    exact hf I.val (by rw [ordinary_weight]; have hlen := boundedWord_weight I; change wordWeight (fun _ => 1) I.val ≤ N at hlen; rw [ordinary_weight] at hlen; omega)

end RothschildStein.G3

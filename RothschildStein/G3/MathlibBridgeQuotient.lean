-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G3.MathlibBridgeFiltration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.G3
variable {a : ℕ}

/-- The fixed augmentation quotient embeds
in the existing finite real coefficient algebra (BB pp. 468–469). -/
def mathlibQuotientMap (a N : ℕ) :
    (FreeAlgebra ℚ (Fin a) ⧸ mathlibAugmentation a ^ (N+1)) →ₐ[ℚ]
      FiniteWordAlgebra a N (fun _ => 1) :=
  Ideal.Quotient.liftₐ _ (mathlibTruncation a N) (by
    intro f hf
    change f ∈ RingHom.ker (mathlibTruncation a N)
    rw [mathlibTruncation_ker]
    exact hf)

/-- Quotient representatives map by coefficient
truncation, with no change to the augmentation power (BB p. 468). -/
@[simp] theorem mathlibQuotientMap_mk (N : ℕ) (f : FreeAlgebra ℚ (Fin a)) :
    mathlibQuotientMap a N (Ideal.Quotient.mk (mathlibAugmentation a ^ (N+1)) f) =
      mathlibTruncation a N f := rfl

/-- Exact kernel identification makes the descent
injective, although its real target has additional coefficients (BB p. 468). -/
theorem mathlibQuotientMap_injective (N : ℕ) : Function.Injective (mathlibQuotientMap a N) := by
  apply (Ideal.injective_lift_iff _).mpr
  exact mathlibTruncation_ker N

/-- Each augmentation representative is genuinely
nilpotent in the fixed quotient, including cutoff zero (BB p. 468). -/
theorem mathlibQuotient_nilpotent (N : ℕ) {f : FreeAlgebra ℚ (Fin a)}
    (hf : f ∈ mathlibAugmentation a) :
    IsNilpotent (Ideal.Quotient.mk (mathlibAugmentation a ^ (N+1)) f) := by
  refine ⟨N+1,?_⟩
  rw [← map_pow,Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hf _

/-- Nilpotent exponentiation transfers exactly
into the existing finite exponential; positivity is discharged by the
augmentation membership (BB pp. 468–469). -/
theorem mathlibQuotientMap_exp (N : ℕ) {f : FreeAlgebra ℚ (Fin a)}
    (hf : f ∈ mathlibAugmentation a) :
    mathlibQuotientMap a N (IsNilpotent.exp
      (Ideal.Quotient.mk (mathlibAugmentation a ^ (N+1)) f)) =
      finiteExp (mathlibTruncation a N f) := by
  rw [IsNilpotent.map_exp (mathlibQuotient_nilpotent N hf),mathlibQuotientMap_mk]
  symm
  exact finiteExp_eq_nilpotentExp
    (ordinaryTrunc_positive ((mem_mathlibAugmentation_iff f).mp hf) N)

end RothschildStein.G3

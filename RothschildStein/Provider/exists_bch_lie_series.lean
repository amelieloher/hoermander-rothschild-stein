-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G3.MathlibBridgeUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.Provider
open RothschildStein.G3

/-- The rational free-Lie BCH series, with uniqueness only
of the associative series (BB Theorems 9.18 and 9.68, pp. 408–409, 469–474). -/
theorem exists_bch_lie_series :
    ∃ C : ℕ → FreeLieAlgebra ℚ (Fin 2),
      C 0 = 0 ∧
      C 1 = FreeLieAlgebra.of ℚ (0 : Fin 2) + FreeLieAlgebra.of ℚ (1 : Fin 2) ∧
      C 2 = (1 / 2 : ℚ) • ⁅FreeLieAlgebra.of ℚ (0 : Fin 2), FreeLieAlgebra.of ℚ (1 : Fin 2)⁆ ∧
      (∀ n : ℕ, C n ∈ Submodule.span ℚ
        {a : FreeLieAlgebra ℚ (Fin 2) | ∃ (l : List (Fin 2)) (j : Fin 2),
          l.length + 1 = n ∧
          a = l.foldr (fun i b => ⁅FreeLieAlgebra.of ℚ i, b⁆) (FreeLieAlgebra.of ℚ j)}) ∧
      (∀ n : ℕ, FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℚ (Fin 2)
          (UniversalEnvelopingAlgebra.ι ℚ (C n)) ∈
        Submodule.span ℚ (Set.range (FreeAlgebra.ι ℚ : Fin 2 → FreeAlgebra ℚ (Fin 2))) ^ n) ∧
      (∀ N : ℕ,
        IsNilpotent.exp (Ideal.Quotient.mk
            (RingHom.ker (FreeAlgebra.algebraMapInv : FreeAlgebra ℚ (Fin 2) →ₐ[ℚ] ℚ) ^ (N + 1))
            (FreeAlgebra.ι ℚ (0 : Fin 2))) *
          IsNilpotent.exp (Ideal.Quotient.mk
            (RingHom.ker (FreeAlgebra.algebraMapInv : FreeAlgebra ℚ (Fin 2) →ₐ[ℚ] ℚ) ^ (N + 1))
            (FreeAlgebra.ι ℚ (1 : Fin 2))) =
        IsNilpotent.exp (Ideal.Quotient.mk
            (RingHom.ker (FreeAlgebra.algebraMapInv : FreeAlgebra ℚ (Fin 2) →ₐ[ℚ] ℚ) ^ (N + 1))
            (∑ n ∈ Finset.Icc 1 N, FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℚ (Fin 2)
          (UniversalEnvelopingAlgebra.ι ℚ (C n))))) ∧
      ∀ S : ℕ → FreeAlgebra ℚ (Fin 2),
        S 0 = 0 →
        (∀ n : ℕ, S n ∈
          Submodule.span ℚ (Set.range (FreeAlgebra.ι ℚ : Fin 2 → FreeAlgebra ℚ (Fin 2))) ^ n) →
        (∀ N : ℕ,
          IsNilpotent.exp (Ideal.Quotient.mk
              (RingHom.ker (FreeAlgebra.algebraMapInv : FreeAlgebra ℚ (Fin 2) →ₐ[ℚ] ℚ) ^ (N + 1))
              (FreeAlgebra.ι ℚ (0 : Fin 2))) *
            IsNilpotent.exp (Ideal.Quotient.mk
              (RingHom.ker (FreeAlgebra.algebraMapInv : FreeAlgebra ℚ (Fin 2) →ₐ[ℚ] ℚ) ^ (N + 1))
              (FreeAlgebra.ι ℚ (1 : Fin 2))) =
          IsNilpotent.exp (Ideal.Quotient.mk
              (RingHom.ker (FreeAlgebra.algebraMapInv : FreeAlgebra ℚ (Fin 2) →ₐ[ℚ] ℚ) ^ (N + 1))
              (∑ n ∈ Finset.Icc 1 N, S n))) →
        ∀ n : ℕ, S n = FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℚ (Fin 2)
          (UniversalEnvelopingAlgebra.ι ℚ (C n)) := by
  refine ⟨mathlibBCHLift, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mathlibBCHLift]
  · simp [mathlibBCHLift]
  · simp [mathlibBCHLift]
  · intro n
    exact mathlibHomogeneousLieSpan_le_frozen n (mathlibBCHLift_mem n)
  · intro n
    rw [← mathlibLieImage_canonical]
    exact mathlibLieImage_mem_generatorSpan_pow (mathlibBCHLift_mem n)
  · intro N
    simp_rw [← mathlibLieImage_canonical]
    exact mathlibBCH_quotient_identity N
  · intro S h0 hS he n
    rw [← mathlibLieImage_canonical]
    exact mathlibBCH_associative_unique S h0 hS he n

end RothschildStein.Provider

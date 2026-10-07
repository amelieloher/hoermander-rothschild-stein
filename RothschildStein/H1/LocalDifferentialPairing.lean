-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.LocalFinitePartialPairing
public import RothschildStein.Definitions.testMultiplierOn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators
namespace RothschildStein.H1
variable {N : ℕ}

/-- Local integration by parts for the fixed finite
smooth differential operator. Each term needs only its own finite
order of differentiability (BB Corollary 6.31, p. 280). -/
theorem integral_differentialOperator_mul_test (U : Opens (Fin N → ℝ))
    (P : SmoothDifferentialOperator N) (f : (Fin N → ℝ) → ℝ)
    (hf : ∀ a ∈ P.indices, ContDiffOn ℝ (∑ j, a j : ℕ) f (U : Set (Fin N → ℝ)))
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    (∫ x in (U : Set (Fin N → ℝ)), P.apply f x * φ x) =
      ∫ x in (U : Set (Fin N → ℝ)), f x * G2.differentialTranspose P φ x := by
  have hX (j : Fin N) : ContDiffOn ℝ (⊤ : ℕ∞) (G2.coordinateFields j)
      (U : Set (Fin N → ℝ)) := contDiffOn_const
  let ψ (a : Fin N → ℕ) (ha : a ∈ P.indices) :=
    testMultiplierOn U (P.coefficient a) (P.smooth_coefficient a ha).contDiffOn φ
  have hψ (a : Fin N → ℕ) (ha : a ∈ P.indices) :
      (ψ a ha : (Fin N → ℝ) → ℝ) = fun x => P.coefficient a x * φ x := by
    funext x
    change φ x * P.coefficient a x = _
    ring
  have hiL (a : Fin N → ℕ) (ha : a ∈ P.indices) : IntegrableOn
      (fun x => (P.coefficient a x * euclideanPartial a f x) * φ x)
      (U : Set (Fin N → ℝ)) volume := by
    have hs := contDiffOn_euclideanPartial_finite U a 0 f (by simpa using hf a ha)
    have hi : IntegrableOn (fun x => euclideanPartial a f x * ψ a ha x)
        (U : Set (Fin N → ℝ)) volume := (S.integrable_mul_test U
      (hs.continuousOn.locallyIntegrableOn U.isOpen.measurableSet) (ψ a ha)).integrableOn
    convert hi using 1
    rw [hψ a ha]
    funext x
    ring
  have hiR (a : Fin N → ℕ) (ha : a ∈ P.indices) : IntegrableOn
      (fun x => f x * ((-1 : ℝ) ^ (∑ j, a j) *
        euclideanPartial a (fun y => P.coefficient a y * φ y) x))
      (U : Set (Fin N → ℝ)) volume := by
    let χ := S.wordDerivativeTest U G2.coordinateFields hX (G2.coordinateWord a) (ψ a ha)
    have hχ : (χ : (Fin N → ℝ) → ℝ) =
        euclideanPartial a (fun y => P.coefficient a y * φ y) := by
      change wordDerivative G2.coordinateFields (G2.coordinateWord a) (ψ a ha) = _
      rw [G2.coordinate_word_partial, hψ a ha]
    have hi : IntegrableOn (fun x => ((-1 : ℝ) ^ (∑ j, a j)) * (f x * χ x))
        (U : Set (Fin N → ℝ)) volume := ((S.integrable_mul_test U ((hf a ha).continuousOn.locallyIntegrableOn
      U.isOpen.measurableSet) χ).integrableOn).const_mul ((-1 : ℝ) ^ (∑ j, a j))
    convert hi using 1
    rw [hχ]
    funext x
    ring
  simp_rw [SmoothDifferentialOperator.apply, Finset.sum_mul,
    G2.differentialTranspose, Finset.mul_sum]
  rw [integral_finsetSum _ hiL, integral_finsetSum _ hiR]
  apply Finset.sum_congr rfl
  intro a ha
  have h := integral_euclideanPartial_mul_test U a f (hf a ha) (ψ a ha)
  rw [hψ a ha] at h
  have hL : (fun x => P.coefficient a x * euclideanPartial a f x * φ x) =
      fun x => euclideanPartial a f x * (P.coefficient a x * φ x) := by funext x; ring
  have hR : (fun x => f x * ((-1 : ℝ) ^ (∑ j, a j) *
      euclideanPartial a (fun y => P.coefficient a y * φ y) x)) =
      fun x => ((-1 : ℝ) ^ (∑ j, a j)) *
        (f x * euclideanPartial a (fun y => P.coefficient a y * φ y) x) := by funext x; ring
  rw [hL, hR, integral_const_mul]
  exact h

end RothschildStein.H1

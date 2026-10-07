-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SmoothingNoDriftStatement
public import RothschildStein.P2.SmoothingSolveEquation
public import RothschildStein.P1.RightParametrixNoDriftPairing

/-!
# Local solvability without drift: the distributional equation and weak derivatives give the equation a.e.

The no-drift counterpart of `SolvabilityFullWeak` for `L = ∑ Xᵢ²` (alphabet `Fin q`, all weights
one): `weakNoDriftEquation_ae_of_solution`: if every `Xᵢ Xᵢ v` exists as a weak word derivative `gsᵢ`
on `V` and the distribution of `v` satisfies `L̃ v = g` in the sense `∫ v L̃ᵀφ = ∫ g φ` for every test
`φ` of `V`, then `∑ᵢ gsᵢ = g` almost everywhere on `V`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2

section WeakNoDrift

variable {N q : ℕ}

/-- The distribution of `v` satisfies `L (ofFun v) = ∑ᵢ gsᵢ` if every `Xᵢ Xᵢ v` exists as a
weak word derivative `gsᵢ` on `V` (`L = ∑ Xᵢ²`). -/
theorem hasDistributionEquation_ofFun_of_weakWords (V : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin N → ℝ)))
    {v : (Fin N → ℝ) → ℝ} {gs : Fin q → (Fin N → ℝ) → ℝ}
    (hs : ∀ i : Fin q, hasWeakWordDeriv X V [i, i] v (gs i)) :
    hasDistributionEquation V X hX (Distribution.ofFun V v volume (⊤ : ℕ∞))
      (fun x => ∑ i, gs i x) := by
  have hsum : LocallyIntegrableOn (fun x => ∑ i, gs i x) (V : Set (Fin N → ℝ)) volume :=
    locallyIntegrableOn_finsetSum Finset.univ (fun i _ => (hs i).2.1)
  refine ⟨hsum, fun φ => ?_⟩
  have e1 : ∀ i : Fin q, Distribution.ofFun V v volume (⊤ : ℕ∞)
      (fieldTransposeTest V (X i) (hX i) (fieldTransposeTest V (X i) (hX i) φ)) =
        Distribution.ofFun V (gs i) volume (⊤ : ℕ∞) φ := by
    intro i
    have := congrArg (fun D : Distribution V ℝ (⊤ : ℕ∞) => D φ)
      (RothschildStein.S.distributionWord_ofFun_eq V X hX [i, i] v (gs i) (hs i))
    simp only [RothschildStein.S.distributionWordCLM_apply,
      fieldTransposeTest_comp_eq_wordTransposeTest_pair] at this
    exact this
  unfold sumSquaresTransposeTest
  rw [map_sum]
  simp_rw [e1]
  rw [← ofFun_finsetSum_apply Finset.univ (fun i _ => (hs i).2.1)]

/-- **The weak equation from the distributional equation, no drift.** If `gsᵢ`
are the weak word derivatives of `v` for the words `[i, i]` on `V`, `v` and `g` are locally
integrable on `V` and `∫_V v L̃ᵀφ = ∫_V g φ` for every test `φ` of `V` (`L = ∑ Xᵢ²`), then
`∑ᵢ gsᵢ = g` almost everywhere on `V`. -/
theorem weakNoDriftEquation_ae_of_solution (V : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin N → ℝ)))
    {v g : (Fin N → ℝ) → ℝ} {gs : Fin q → (Fin N → ℝ) → ℝ}
    (hs : ∀ i : Fin q, hasWeakWordDeriv X V [i, i] v (gs i))
    (hvloc : LocallyIntegrableOn v (V : Set (Fin N → ℝ)) volume)
    (hg : LocallyIntegrableOn g (V : Set (Fin N → ℝ)) volume)
    (hsol : ∀ φ : TestFunction V ℝ (⊤ : ℕ∞),
      ∫ ξ in (V : Set (Fin N → ℝ)), v ξ * sumSquaresTranspose X φ ξ =
        ∫ ξ in (V : Set (Fin N → ℝ)), g ξ * φ ξ) :
    ∀ᵐ x ∂(volume.restrict (V : Set (Fin N → ℝ))), (∑ i, gs i x) = g x := by
  have hD := hasDistributionEquation_ofFun_of_weakWords V X hX hs
  refine Distribution.ofFun_injective (n := (⊤ : ℕ∞)) hD.1 hg ?_
  ext φ
  rw [← hD.2 φ, Distribution.ofFun_apply hvloc, Distribution.ofFun_apply hg]
  have hcoe : ∀ x, sumSquaresTransposeTest V X hX φ x = sumSquaresTranspose X φ x := fun x =>
    congrFun (P1.sumSquaresTransposeTest_coe_noDrift V X hX φ) x
  have e1 : ∫ x, (sumSquaresTransposeTest V X hX φ) x • v x =
      ∫ ξ in (V : Set (Fin N → ℝ)), v ξ * sumSquaresTranspose X φ ξ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (V : Set (Fin N → ℝ)))
      (fun x hx => by
        have := (sumSquaresTransposeTest V X hX φ).zero_on_compl hx
        simp [this])]
    refine setIntegral_congr_fun V.isOpen.measurableSet (fun x _ => ?_)
    simp only [smul_eq_mul, hcoe]
    ring
  have e2 : ∫ x, φ x • g x = ∫ ξ in (V : Set (Fin N → ℝ)), g ξ * φ ξ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (V : Set (Fin N → ℝ)))
      (fun x hx => by
        have := φ.zero_on_compl hx
        simp [this])]
    refine setIntegral_congr_fun V.isOpen.measurableSet (fun x _ => ?_)
    simp only [smul_eq_mul]
    ring
  rw [e1, e2]
  exact hsol φ

/-- The words `[i, i]` have weight two for the no-drift weights. -/
theorem mem_wordFamily_noDrift_sq (i : Fin q) :
    ([i, i] : List (Fin q)) ∈ wordFamily noDriftWeight 2 := by
  rw [RothschildStein.S.mem_wordFamily_iff]
  simp [wordWeight, noDriftWeight]

/-- The pairing `∫ v L̃ᵀφ` of a test `φ` of `U` is the same over any measurable `T ⊇ U`, no
drift (the transpose is a test of `U`, so vanishes outside `U`). -/
theorem setIntegral_mul_sumSquaresTranspose_eq (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ))) {T : Set (Fin N → ℝ)}
    (hT : MeasurableSet T) (hUT : (U : Set (Fin N → ℝ)) ⊆ T) (v : (Fin N → ℝ) → ℝ)
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    ∫ ξ in T, v ξ * sumSquaresTranspose X φ ξ =
      ∫ ξ in (U : Set (Fin N → ℝ)), v ξ * sumSquaresTranspose X φ ξ := by
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hT hUT (fun x hx => ?_)
  have hcoe := congrFun (P1.sumSquaresTransposeTest_coe_noDrift U X hX φ) x
  have h0 := (sumSquaresTransposeTest U X hX φ).zero_on_compl
    (show x ∈ (U : Set (Fin N → ℝ))ᶜ from hx.2)
  rw [← hcoe]
  simp [h0]

end WeakNoDrift

end RothschildStein.P2

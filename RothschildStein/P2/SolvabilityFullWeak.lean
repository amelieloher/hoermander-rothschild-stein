-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SmoothingSolveEquation
public import RothschildStein.P1.RightParametrixPairing

/-!
# Local solvability, `L^p` solutions: the distributional equation and weak derivatives give the equation a.e.

`weakDriftEquation_ae_of_solution`: if `X₀ v` and `Xᵢ Xᵢ v` exist as weak word derivatives `g₀`,
`gsᵢ` on `V` (for instance, if `v ∈ W^{2,p}_{X̃}(V)` or `v ∈ C^{2,α}_{X̃}(V)`, BB Prop 2.22) and the
distribution of `v` satisfies `L̃ v = g` in the sense `∫ v L̃ᵀφ = ∫ g φ` for every test `φ` of `V`, then
`(∑ᵢ gsᵢ) + g₀ = g` almost everywhere on `V` (the fundamental lemma, applied to the weak form of
`L̃ v`, by the definition of weak derivatives: `L̃ v = g` on `U_r`, in distributions and a.e.).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2

section Weak

variable {N q : ℕ}

/-- **The weak equation from the distributional equation.** If `g₀`, `gsᵢ` are
the weak word derivatives of `v` for the words `[0]`, `[i+1, i+1]` on `V`, `g` is locally integrable
on `V` and `∫_V v L̃ᵀφ = ∫_V g φ` for every test `φ` of `V`, then `(∑ᵢ gsᵢ) + g₀ = g` almost
everywhere on `V`. -/
theorem weakDriftEquation_ae_of_solution (V : Opens (Fin N → ℝ))
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin N → ℝ)))
    {v g g₀ : (Fin N → ℝ) → ℝ} {gs : Fin q → (Fin N → ℝ) → ℝ}
    (h0 : hasWeakWordDeriv X V [0] v g₀)
    (hs : ∀ i : Fin q, hasWeakWordDeriv X V [i.succ, i.succ] v (gs i))
    (hg : LocallyIntegrableOn g (V : Set (Fin N → ℝ)) volume)
    (hsol : ∀ φ : TestFunction V ℝ (⊤ : ℕ∞),
      ∫ ξ in (V : Set (Fin N → ℝ)), v ξ * sumSquaresWithDriftTranspose X φ ξ =
        ∫ ξ in (V : Set (Fin N → ℝ)), g ξ * φ ξ) :
    ∀ᵐ x ∂(volume.restrict (V : Set (Fin N → ℝ))), (∑ i, gs i x) + g₀ x = g x := by
  have hv : weakDriftEquation V X v (fun x => (∑ i, gs i x) + g₀ x) :=
    ⟨g₀, gs, h0, hs, Filter.Eventually.of_forall fun _ => rfl⟩
  have hD := hasDistributionEquationWithDrift_ofFun_of_weakDriftEquation V X hX hv
  have hvloc : LocallyIntegrableOn v (V : Set (Fin N → ℝ)) volume := h0.1
  refine Distribution.ofFun_injective (n := (⊤ : ℕ∞)) hD.1 hg ?_
  ext φ
  rw [← hD.2 φ, Distribution.ofFun_apply hvloc, Distribution.ofFun_apply hg]
  have hcoe : ∀ x, sumSquaresWithDriftTransposeTest V X hX φ x =
      sumSquaresWithDriftTranspose X φ x := fun x =>
    congrFun (P1.sumSquaresWithDriftTransposeTest_coe V X hX φ) x
  have e1 : ∫ x, (sumSquaresWithDriftTransposeTest V X hX φ) x • v x =
      ∫ ξ in (V : Set (Fin N → ℝ)), v ξ * sumSquaresWithDriftTranspose X φ ξ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (V : Set (Fin N → ℝ)))
      (fun x hx => by
        have := (sumSquaresWithDriftTransposeTest V X hX φ).zero_on_compl hx
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

/-- The word `[0]` has weight two. -/
theorem mem_wordFamily_drift_zero : ([0] : List (Fin (q + 1))) ∈ wordFamily driftWeight 2 := by
  rw [RothschildStein.S.mem_wordFamily_iff]
  simp [wordWeight, driftWeight]

/-- The words `[i+1, i+1]` have weight two. -/
theorem mem_wordFamily_drift_succ_succ (i : Fin q) :
    ([i.succ, i.succ] : List (Fin (q + 1))) ∈ wordFamily driftWeight 2 := by
  rw [RothschildStein.S.mem_wordFamily_iff]
  simp [wordWeight, driftWeight]

/-- The pairing `∫ v L̃ᵀφ` of a test `φ` of `U` is the same over any measurable `T ⊇ U`
(the transpose is a test of `U`, so vanishes outside `U`). -/
theorem setIntegral_mul_sumSquaresWithDriftTranspose_eq (U : Opens (Fin N → ℝ))
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ))) {T : Set (Fin N → ℝ)}
    (hT : MeasurableSet T) (hUT : (U : Set (Fin N → ℝ)) ⊆ T) (v : (Fin N → ℝ) → ℝ)
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    ∫ ξ in T, v ξ * sumSquaresWithDriftTranspose X φ ξ =
      ∫ ξ in (U : Set (Fin N → ℝ)), v ξ * sumSquaresWithDriftTranspose X φ ξ := by
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hT hUT (fun x hx => ?_)
  have hcoe := congrFun (P1.sumSquaresWithDriftTransposeTest_coe U X hX φ) x
  have h0 := (sumSquaresWithDriftTransposeTest U X hX φ).zero_on_compl
    (show x ∈ (U : Set (Fin N → ℝ))ᶜ from hx.2)
  rw [← hcoe]
  simp [h0]

end Weak

end RothschildStein.P2

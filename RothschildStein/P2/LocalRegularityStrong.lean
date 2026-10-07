-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularitySolvability

/-!
# The representatives solve the equation strongly

The local regularity theorem asserts that the representatives given by the distributional smoothing theorem solve `L u = f` strongly (BB pp. 536-537):
almost everywhere with weak derivatives in the Sobolev case, and with intrinsic derivatives at
every point in the Hölder case.

* `ae_eq_sum_weakDerivs_drift` / `ae_eq_sum_weakDerivs_noDrift`: if `ofFun u`
  satisfies the distributional equation `L (ofFun u) = f` on an open set `V` and `u` has weak word
  derivatives `g i` for the words of `L` (`driftOpWords q`, `noDriftOpWords q`), then
  `f = ∑ᵢ g i` almost everywhere on `V`. The weak equation `∑ g i = f` of the weak derivatives is
  a distributional equation with right-hand side `∑ g i` (`hasDistributionEquation…_ofFun_of_weak…`),
  and `Distribution.ofFun_injective` identifies the two right-hand sides.
* `hasWeakOperatorValue_*`: the same as `HasWeakOperatorValue`, with the words of `L` read off the
  Sobolev space `W^{2,p}_X(V)`.
* `eqOn_sum_weakDerivs_*` (`Measure.eqOn_open_of_ae_eq`): if the weak derivatives `g i` are
  continuous (they are also intrinsic derivatives) and `f` is continuous, the a.e. equation
  holds at every point of `V`: `∑ᵢ g i x = f x`, i.e. `HasIntrinsicOperatorValue X V (…) u f`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2

section Restriction

variable {n : ℕ}

/-- The restriction of the regular distribution of a locally integrable function to a smaller open
set is the regular distribution of the same function. -/
theorem distributionRestrictionCLM_ofFun (Ω V : Opens (Fin n → ℝ)) (hVΩ : V ≤ Ω)
    {u : (Fin n → ℝ) → ℝ} (hu : LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume) :
    RothschildStein.S.distributionRestrictionCLM Ω V (Distribution.ofFun Ω u volume (⊤ : ℕ∞)) =
      Distribution.ofFun V u volume (⊤ : ℕ∞) := by
  ext φ
  rw [RothschildStein.S.distributionRestrictionCLM_apply Ω V hVΩ,
    Distribution.ofFun_apply hu, Distribution.ofFun_apply (hu.mono_set hVΩ)]
  rfl

end Restriction

section Drift

variable {n q : ℕ}

/-- If `ofFun u` solves `L (ofFun u) = f` on `V`
(`L = ∑ Xᵢ² + X₀`) and `u` has the weak word derivatives `g i` of the words of `L`, then
`f = ∑ᵢ g i` almost everywhere on `V`. -/
theorem ae_eq_sum_weakDerivs_drift (V : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {u f : (Fin n → ℝ) → ℝ}
    (hT : hasDistributionEquationWithDrift V X hX (Distribution.ofFun V u volume (⊤ : ℕ∞)) f)
    {g : Fin (q + 1) → (Fin n → ℝ) → ℝ}
    (hg : ∀ i, hasWeakWordDeriv X V (driftOpWords q i) u (g i)) :
    f =ᵐ[volume.restrict (V : Set (Fin n → ℝ))] fun x => ∑ i, g i x := by
  have h0 : hasWeakWordDeriv X V [0] u (g 0) := by simpa [driftOpWords] using hg 0
  have hs : ∀ i : Fin q, hasWeakWordDeriv X V [i.succ, i.succ] u (g i.succ) := fun i => by
    simpa [driftOpWords, Fin.succ_ne_zero] using hg i.succ
  have hweak : weakDriftEquation V X u (fun x => (∑ i : Fin q, g i.succ x) + g 0 x) :=
    ⟨g 0, fun i => g i.succ, h0, hs, Eventually.of_forall fun x => rfl⟩
  have hD := hasDistributionEquationWithDrift_ofFun_of_weakDriftEquation V X hX hweak
  have heq : Distribution.ofFun V f volume (⊤ : ℕ∞) =
      Distribution.ofFun V (fun x => (∑ i : Fin q, g i.succ x) + g 0 x) volume (⊤ : ℕ∞) := by
    ext φ
    exact (hT.2 φ).symm.trans (hD.2 φ)
  have hae := Distribution.ofFun_injective hT.1 hD.1 heq
  refine hae.trans (Eventually.of_forall fun x => ?_)
  simp only [Fin.sum_univ_succ]
  ring

/-- The operator value of a solution with weak word
derivatives of the words of `L`. -/
theorem hasWeakOperatorValue_drift_of_equation (V : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {u f : (Fin n → ℝ) → ℝ}
    (hT : hasDistributionEquationWithDrift V X hX (Distribution.ofFun V u volume (⊤ : ℕ∞)) f)
    {p : ℝ≥0∞} (hu : memSobolevX driftWeight X V 2 p u) :
    HasWeakOperatorValue X V (driftOpWords q) u f := by
  choose g hg using fun i => hu.2 (driftOpWords q i) (driftOpWords_mem_wordFamily q i)
  exact ⟨g, fun i => (hg i).1, ae_eq_sum_weakDerivs_drift V X hX hT fun i => (hg i).1⟩

/-- If the weak derivatives `g i` of the words of `L` are
continuous and `f` is continuous on `V`, then `L u = ∑ᵢ g i = f` holds at every point of `V`
(`Measure.eqOn_open_of_ae_eq`). -/
theorem eqOn_sum_weakDerivs_drift (V : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {u f : (Fin n → ℝ) → ℝ}
    (hT : hasDistributionEquationWithDrift V X hX (Distribution.ofFun V u volume (⊤ : ℕ∞)) f)
    (hfc : ContinuousOn f (V : Set (Fin n → ℝ)))
    {g : Fin (q + 1) → (Fin n → ℝ) → ℝ}
    (hgc : ∀ i, ContinuousOn (g i) (V : Set (Fin n → ℝ)))
    (hgw : ∀ i, hasWeakWordDeriv X V (driftOpWords q i) u (g i)) :
    ∀ x ∈ (V : Set (Fin n → ℝ)), ∑ i, g i x = f x := by
  have hae := ae_eq_sum_weakDerivs_drift V X hX hT hgw
  have hsc : ContinuousOn (fun x => ∑ i, g i x) (V : Set (Fin n → ℝ)) :=
    continuousOn_finsetSum Finset.univ fun i _ => hgc i
  have heq := Measure.eqOn_open_of_ae_eq hae V.isOpen hfc hsc
  exact fun x hx => (heq hx).symm

end Drift

section NoDrift

variable {n q : ℕ}

/-- If `ofFun u` solves `L (ofFun u) = f` on `V`
(`L = ∑ Xᵢ²`) and `u` has the weak word derivatives `g i` of the words of `L`, then
`f = ∑ᵢ g i` almost everywhere on `V`. -/
theorem ae_eq_sum_weakDerivs_noDrift (V : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {u f : (Fin n → ℝ) → ℝ}
    (hT : hasDistributionEquation V X hX (Distribution.ofFun V u volume (⊤ : ℕ∞)) f)
    {g : Fin q → (Fin n → ℝ) → ℝ}
    (hg : ∀ i, hasWeakWordDeriv X V (noDriftOpWords q i) u (g i)) :
    f =ᵐ[volume.restrict (V : Set (Fin n → ℝ))] fun x => ∑ i, g i x := by
  have hweak : weakNoDriftEquation V X u (fun x => ∑ i, g i x) :=
    ⟨g, fun i => hg i, Eventually.of_forall fun x => rfl⟩
  have hD := hasDistributionEquation_ofFun_of_weakNoDriftEquation V X hX hweak
  have heq : Distribution.ofFun V f volume (⊤ : ℕ∞) =
      Distribution.ofFun V (fun x => ∑ i, g i x) volume (⊤ : ℕ∞) := by
    ext φ
    exact (hT.2 φ).symm.trans (hD.2 φ)
  exact Distribution.ofFun_injective hT.1 hD.1 heq

/-- The operator value of a solution with weak word
derivatives of the words of `L`. -/
theorem hasWeakOperatorValue_noDrift_of_equation (V : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {u f : (Fin n → ℝ) → ℝ}
    (hT : hasDistributionEquation V X hX (Distribution.ofFun V u volume (⊤ : ℕ∞)) f)
    {p : ℝ≥0∞} (hu : memSobolevX noDriftWeight X V 2 p u) :
    HasWeakOperatorValue X V (noDriftOpWords q) u f := by
  choose g hg using fun i => hu.2 (noDriftOpWords q i) (noDriftOpWords_mem_wordFamily q i)
  exact ⟨g, fun i => (hg i).1, ae_eq_sum_weakDerivs_noDrift V X hX hT fun i => (hg i).1⟩

/-- If the weak derivatives `g i` of the words of `L` are
continuous and `f` is continuous on `V`, then `L u = ∑ᵢ g i = f` holds at every point of `V`
(`Measure.eqOn_open_of_ae_eq`). -/
theorem eqOn_sum_weakDerivs_noDrift (V : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {u f : (Fin n → ℝ) → ℝ}
    (hT : hasDistributionEquation V X hX (Distribution.ofFun V u volume (⊤ : ℕ∞)) f)
    (hfc : ContinuousOn f (V : Set (Fin n → ℝ)))
    {g : Fin q → (Fin n → ℝ) → ℝ}
    (hgc : ∀ i, ContinuousOn (g i) (V : Set (Fin n → ℝ)))
    (hgw : ∀ i, hasWeakWordDeriv X V (noDriftOpWords q i) u (g i)) :
    ∀ x ∈ (V : Set (Fin n → ℝ)), ∑ i, g i x = f x := by
  have hae := ae_eq_sum_weakDerivs_noDrift V X hX hT hgw
  have hsc : ContinuousOn (fun x => ∑ i, g i x) (V : Set (Fin n → ℝ)) :=
    continuousOn_finsetSum Finset.univ fun i _ => hgc i
  have heq := Measure.eqOn_open_of_ae_eq hae V.isOpen hfc hsc
  exact fun x hx => (heq hx).symm

end NoDrift

end RothschildStein.P2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LocalEnergy
import Mathlib.Tactic.Linter

/-! # Assembling weak horizontal derivatives from relatively compact open sets -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace RothschildStein

namespace HeatKernel

/-- Weak derivatives on every relatively compact open subset give a weak derivative on the
ambient open set. Each test is contained in one such subset. -/
theorem hasWeakWordDeriv_of_precompact_restrictions {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (I : List (Fin q)) {f g : (Fin N → ℝ) → ℝ}
    (h : ∀ V : Opens (Fin N → ℝ), IsCompact (closure (V : Set (Fin N → ℝ))) →
      closure (V : Set (Fin N → ℝ)) ⊆ (U : Set (Fin N → ℝ)) → hasWeakWordDeriv X V I f g) :
    hasWeakWordDeriv X U I f g := by
  have hf : LocallyIntegrableOn f (U : Set (Fin N → ℝ)) volume := by
    apply (locallyIntegrableOn_iff U.isOpen.isLocallyClosed).mpr
    intro K hKU hc
    obtain ⟨V, hKV, hVc, hVU⟩ := exists_precompact_open_of_isCompact U hc hKU
    exact (h V hVc hVU).1.integrableOn_compact_subset hKV hc
  have hg : LocallyIntegrableOn g (U : Set (Fin N → ℝ)) volume := by
    apply (locallyIntegrableOn_iff U.isOpen.isLocallyClosed).mpr
    intro K hKU hc
    obtain ⟨V, hKV, hVc, hVU⟩ := exists_precompact_open_of_isCompact U hc hKU
    exact (h V hVc hVU).2.1.integrableOn_compact_subset hKV hc
  refine ⟨hf, hg, fun φ => ?_⟩
  obtain ⟨V, hKV, hVc, hVU⟩ := exists_precompact_open_of_isCompact U
    φ.hasCompactSupport φ.tsupport_subset
  let ψ : TestFunction V ℝ (⊤ : ℕ∞) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hKV⟩
  have he := (h V hVc hVU).2.2 ψ
  have hgz : ∀ x ∉ (V : Set (Fin N → ℝ)), g x * φ x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hKV ht)), mul_zero]
  have hfz : ∀ x ∉ (V : Set (Fin N → ℝ)), f x * wordTranspose X I φ x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hKV (S.tsupport_wordTranspose_subset X I φ ht))), mul_zero]
  have hgzU : ∀ x ∉ (U : Set (Fin N → ℝ)), g x * φ x = 0 :=
    fun x hx => hgz x (fun hv => hx (hVU (subset_closure hv)))
  have hfzU : ∀ x ∉ (U : Set (Fin N → ℝ)), f x * wordTranspose X I φ x = 0 :=
    fun x hx => hfz x (fun hv => hx (hVU (subset_closure hv)))
  change (∫ x in (V : Set (Fin N → ℝ)), g x * φ x) =
    ∫ x in (V : Set (Fin N → ℝ)), f x * wordTranspose X I φ x at he
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hgz,
    setIntegral_eq_integral_of_forall_compl_eq_zero hfz] at he
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hgzU,
    setIntegral_eq_integral_of_forall_compl_eq_zero hfzU]
  exact he

end HeatKernel

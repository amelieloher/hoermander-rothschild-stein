-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Locality

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n m : ℕ}

/-- Compactly supported weak words extend by zero to a larger open set
(BB pp. 593, 606). -/
theorem hasWeakWordDeriv_zeroExtension
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω U : Opens (Fin n → ℝ)) (hU : (U : Set (Fin n → ℝ)) ⊆ Ω)
    (K : Compacts (Fin n → ℝ)) (hK : (K : Set (Fin n → ℝ)) ⊆ U)
    (I : List (Fin m)) (f g : (Fin n → ℝ) → ℝ)
    (h : hasWeakWordDeriv X U I f g)
    (hf : ∀ᵐ x ∂volume, x ∈ (U : Set (Fin n → ℝ)) → x ∉ K → f x = 0) :
    hasWeakWordDeriv X Ω I ((U : Set (Fin n → ℝ)).indicator f)
      ((U : Set (Fin n → ℝ)).indicator g) := by
  let V : Opens (Fin n → ℝ) := ⟨(U : Set (Fin n → ℝ)) \ K,
    U.isOpen.sdiff K.isCompact.isClosed⟩
  have hfV : f =ᵐ[volume.restrict (V : Set (Fin n → ℝ))] (fun _ => 0) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' V.isOpen.measurableSet]
    filter_upwards [hf] with x hx
    exact fun hmem => hx hmem.1 hmem.2
  have hgV := hasWeakWordDeriv_locality X U V (fun _ hx => hx.1) h hfV
  have hg : ∀ᵐ x ∂volume, x ∈ (U : Set (Fin n → ℝ)) → x ∉ K → g x = 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' V.isOpen.measurableSet] at hgV
    filter_upwards [hgV] with x hx
    exact fun hu hk => hx ⟨hu, hk⟩
  have hfi := integrable_zeroExtension_of_compact_support U K hK f h.1 hf
  have hgi := integrable_zeroExtension_of_compact_support U K hK g h.2.1 hg
  refine ⟨hfi.locallyIntegrable.locallyIntegrableOn _,
    hgi.locallyIntegrable.locallyIntegrableOn _, fun φ => ?_⟩
  obtain ⟨χ, W, hW, hKW, _, hone⟩ := exists_test_plateau U K hK
  let ψ : TestFunction U ℝ (⊤ : ℕ∞) := testMultiplierOn U φ φ.contDiff.contDiffOn χ
  have heK : ∀ x ∈ (K : Set (Fin n → ℝ)), wordTranspose X I ψ x = wordTranspose X I φ x := by
    intro x hx
    have hp : (ψ : (Fin n → ℝ) → ℝ) =ᶠ[𝓝 x] φ := by
      filter_upwards [hW.mem_nhds (hKW hx)] with y hy
      change χ y * φ y = φ y
      rw [hone hy]
      simp
    exact (wordTranspose_eventuallyEq X I hp).self_of_nhds
  have hl : (fun x => (U : Set (Fin n → ℝ)).indicator g x * φ x) =ᵐ[volume]
      fun x => g x * ψ x := by
    filter_upwards [hg] with x hx
    by_cases hu : x ∈ (U : Set (Fin n → ℝ))
    · by_cases hk : x ∈ (K : Set (Fin n → ℝ))
      · change (U : Set (Fin n → ℝ)).indicator g x * φ x = g x * (χ x * φ x)
        rw [Set.indicator_of_mem hu, hone (hKW hk)]
        simp
      · simp [hu, hx hu hk]
    · simp [hu, ψ.zero_on_compl hu]
  have hr : (fun x => (U : Set (Fin n → ℝ)).indicator f x * wordTranspose X I φ x) =ᵐ[volume]
      fun x => f x * wordTranspose X I ψ x := by
    filter_upwards [hf] with x hx
    by_cases hu : x ∈ (U : Set (Fin n → ℝ))
    · by_cases hk : x ∈ (K : Set (Fin n → ℝ))
      · rw [Set.indicator_of_mem hu, heK x hk]
      · simp [hu, hx hu hk]
    · have hz : wordTranspose X I ψ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hu (ψ.tsupport_subset (tsupport_wordTranspose_subset X I ψ ht)))
      simp [hu, hz]
  have hlΩ : ∀ x, x ∉ (Ω : Set (Fin n → ℝ)) →
      (U : Set (Fin n → ℝ)).indicator g x * φ x = 0 := by
    intro x hx
    simp [Set.indicator_of_notMem (fun hu => hx (hU hu))]
  have hrΩ : ∀ x, x ∉ (Ω : Set (Fin n → ℝ)) →
      (U : Set (Fin n → ℝ)).indicator f x * wordTranspose X I φ x = 0 := by
    intro x hx
    simp [Set.indicator_of_notMem (fun hu => hx (hU hu))]
  have hlU : ∀ x, x ∉ (U : Set (Fin n → ℝ)) → g x * ψ x = 0 := by
    intro x hx
    simp [ψ.zero_on_compl hx]
  have hrU : ∀ x, x ∉ (U : Set (Fin n → ℝ)) → f x * wordTranspose X I ψ x = 0 := by
    intro x hx
    have hz : wordTranspose X I ψ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hx (ψ.tsupport_subset (tsupport_wordTranspose_subset X I ψ ht)))
    simp [hz]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hlΩ,
    setIntegral_eq_integral_of_forall_compl_eq_zero hrΩ,
    integral_congr_ae hl, integral_congr_ae hr,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hlU,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hrU]
  exact h.2.2 ψ

end RothschildStein.S

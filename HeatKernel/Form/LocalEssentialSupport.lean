-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.EssentialSupportZeroBoundary
public import HeatKernel.Form.LocalEnergy
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Linter

/-! # Extending compactly supported local energy functions by zero -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace HeatKernel

/-- A local energy function which vanishes off a compact subset of its domain extends by zero
to the global energy domain, with zero boundary values on the original open set. -/
theorem MemLocalEnergy.exists_zeroBoundaryGraph_extension {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {f : (Fin N → ℝ) → ℝ}
    (hf : MemLocalEnergy U X f) {K : Set (Fin N → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hz : ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), x ∉ K → f x = 0) :
    ∃ u : energyGraph (N := N) ⊤ X,
      (u : GradientSpace (N := N) ⊤ q) ∈ zeroBoundaryGraph U X ∧
      (u : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] (U : Set (Fin N → ℝ)).indicator f := by
  obtain ⟨V, hKV, hVc, hVU⟩ := exists_precompact_open_of_isCompact U hK hKU
  obtain ⟨φ, hφ, _, hs, hone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) V.isOpen hK.isClosed hKV
  have ht : tsupport φ = closure (V : Set (Fin N → ℝ)) := by
    rw [tsupport, hs]
  have hc : HasCompactSupport φ := by
    change IsCompact (tsupport φ)
    rw [ht]
    exact hVc
  obtain ⟨u, hu⟩ := hf.exists_mul_smooth_compact U X hX hφ hc (ht ▸ hVU)
  have he : (u : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      (U : Set (Fin N → ℝ)).indicator f := by
    filter_upwards [hu, ae_imp_of_ae_restrict hz] with x hx hxz
    rw [hx]
    by_cases hxu : x ∈ (U : Set (Fin N → ℝ))
    · rw [indicator_of_mem hxu]
      by_cases hxK : x ∈ K
      · rw [(hone x).mp hxK, mul_one]
      · rw [hxz hxu hxK, zero_mul]
    · rw [indicator_of_notMem hxu]
      have hp : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxu ((ht ▸ hVU) h))
      rw [hp, mul_zero]
  have huo : ∀ᵐ x ∂volume, x ∉ K → (u : GradientSpace (N := N) ⊤ q).fst x = 0 := by
    filter_upwards [he, ae_imp_of_ae_restrict hz] with x hx hxz hxK
    rw [hx]
    by_cases hxu : x ∈ (U : Set (Fin N → ℝ))
    · rw [indicator_of_mem hxu, hxz hxu hxK]
    · exact indicator_of_notMem hxu f
  exact ⟨u, mem_zeroBoundaryGraph_of_ae_zero_off_compact U X hX u hK hKU huo, he⟩



end HeatKernel

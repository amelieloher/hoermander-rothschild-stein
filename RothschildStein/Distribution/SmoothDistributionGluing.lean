-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.RepresentativeOverlap
public import RothschildStein.Distribution.CompatibleSmoothGluing
public import RothschildStein.Distribution.LocalTestVanishing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.Distribution

/-- smooth local representatives on an arbitrary open
cover glue to one smooth representative of the actual distribution.
The final test identity follows from finite partitions of compact
supports, rather than any countability assumption on the cover. -/
theorem exists_smooth_distribution_gluing {N : ℕ} {ι : Type*}
    (Ω : Opens (Fin N → ℝ)) (T : Distribution Ω ℂ (⊤ : ℕ∞))
    (U : ι → Set (Fin N → ℝ)) (f : ι → (Fin N → ℝ) → ℂ)
    (hUopen : ∀ i, IsOpen (U i)) (hUsub : ∀ i, U i ⊆ Ω)
    (hcover : ∀ x ∈ (Ω : Set (Fin N → ℝ)), ∃ i, x ∈ U i)
    (hf : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (f i) (U i))
    (hrep : ∀ i, ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), tsupport ψ ⊆ U i →
      T ψ = ∫ x, ψ x • f i x) :
    ∃ F : (Fin N → ℝ) → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F (Ω : Set (Fin N → ℝ)) ∧
      ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T ψ = ∫ x, ψ x • F x := by
  have hcompat (i j : ι) : EqOn (f i) (f j) (U i ∩ U j) :=
    distributionRepresentatives_agree_on_overlap Ω T (U i) (U j) (hUopen i) (hUopen j)
      (hUsub i) (hUsub j) (f i) (f j) (hf i).continuousOn (hf j).continuousOn (hrep i) (hrep j)
  obtain ⟨F, hF, hEq⟩ := exists_complex_smooth_gluing (Ω : Set (Fin N → ℝ)) Ω.isOpen
    U f hUopen hUsub hcover hf hcompat
  have hFi : LocallyIntegrableOn F (Ω : Set (Fin N → ℝ)) volume :=
    hF.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hz : T - Distribution.ofFun Ω F volume (⊤ : ℕ∞) = 0 := by
    apply distribution_eq_zero_of_local_test_vanishing
    intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    refine ⟨U i, hUopen i, hi, fun ψ hψ => ?_⟩
    change T ψ - Distribution.ofFun Ω F volume (⊤ : ℕ∞) ψ = 0
    rw [Distribution.ofFun_apply hFi, hrep i ψ hψ]
    apply sub_eq_zero.mpr
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ U i
    · rw [hEq i hy]
    · have hzero : ψ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hψ h))
      rw [hzero, zero_smul, zero_smul]
  have hT := sub_eq_zero.mp hz
  refine ⟨F, hF, fun ψ => ?_⟩
  rw [hT, Distribution.ofFun_apply hFi]

end RothschildStein.Distribution

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactKernelDerivativeLocal
public import RothschildStein.S.ProductSectionDerivative
public import RothschildStein.S.Locality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter Metric TopologicalSpace
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Smooth compact-kernel integration of data merely locally
integrable on an open domain; the common support is an interior compact
set (BB pp. 75–78; domain). -/
theorem contDiffOn_compactKernelIntegral_of_local_data
    (Ω : Opens (Fin n → ℝ)) (K : Compacts (Fin n → ℝ))
    (hK : (K : Set (Fin n → ℝ)) ⊆ Ω) {U : Set P} (hU : IsOpen U)
    {k : P → (Fin n → ℝ) → ℝ}
    (hks : ∀ x z, x ∈ U → z ∉ K → k x z = 0)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) (uncurry k) (U ×ˢ univ))
    {h : (Fin n → ℝ) → ℝ} (hh : LocallyIntegrableOn h (Ω : Set (Fin n → ℝ)) volume) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ∫ z, h z * k x z) U := by
  obtain ⟨χ,W,hW,hKW,hWΩ,hχ⟩ := exists_test_plateau Ω K hK
  have hi : Integrable (fun z => h z * χ z) volume := integrable_mul_test Ω hh χ
  have H := contDiffOn_compactKernelIntegral hU K.isCompact hks hk hi.locallyIntegrable
  apply H.congr
  intro x hx
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  by_cases hz : z ∈ (K : Set (Fin n → ℝ))
  · have hc : χ z = 1 := hχ (hKW hz)
    change h z * k x z = (h z * χ z) * k x z
    rw [hc,mul_one]
  · change h z * k x z = (h z * χ z) * k x z
    rw [hks x z hx hz]
    simp only [MulZeroClass.mul_zero]

/-- The local-data derivative formula has no global integrability
premise: a cutoff on the common interior compact support discharges it
(BB p. 78; weak transfer). -/
theorem fderiv_compactKernelIntegral_apply_of_local_data [FiniteDimensional ℝ P]
    (Ω : Opens (Fin n → ℝ)) (K : Compacts (Fin n → ℝ))
    (hK : (K : Set (Fin n → ℝ)) ⊆ Ω)
    {k : P → (Fin n → ℝ) → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) (uncurry k))
    {h : (Fin n → ℝ) → ℝ} (hh : LocallyIntegrableOn h (Ω : Set (Fin n → ℝ)) volume)
    (x v : P) {r : ℝ} (hr : 0 < r)
    (hks : ∀ a z, a ∈ ball x r → z ∉ K → k a z = 0) :
    fderiv ℝ (fun a => ∫ z, h z * k a z) x v =
      ∫ z, h z * fderiv ℝ (uncurry k) (x,z) (v,0) := by
  obtain ⟨χ,W,hW,hKW,hWΩ,hχ⟩ := exists_test_plateau Ω K hK
  have hi : Integrable (fun z => h z * χ z) volume := integrable_mul_test Ω hh χ
  have he : (fun a => ∫ z, (h z * χ z) * k a z) =ᶠ[𝓝 x]
      (fun a => ∫ z, h z * k a z) := by
    filter_upwards [ball_mem_nhds x hr] with a ha
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    change (h z * χ z) * k a z = h z * k a z
    by_cases hz : z ∈ (K : Set (Fin n → ℝ))
    · have hc : χ z = 1 := hχ (hKW hz)
      rw [hc,mul_one]
    · rw [hks a z ha hz]
      simp only [MulZeroClass.mul_zero]
  rw [← he.fderiv_eq,
    fderiv_compactKernelIntegral_apply_of_support_near K.isCompact hk hi.locallyIntegrable x v hr hks]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  change (h z * χ z) * fderiv ℝ (uncurry k) (x,z) (v,0) =
    h z * fderiv ℝ (uncurry k) (x,z) (v,0)
  by_cases hz : z ∈ (K : Set (Fin n → ℝ))
  · have hc : χ z = 1 := hχ (hKW hz)
    rw [hc,mul_one]
  · have hzero : (fun a => k a z) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [ball_mem_nhds x hr] with a ha
      exact hks a z ha hz
    have hd : fderiv ℝ (uncurry k) (x,z) (v,0) = 0 := by
      rw [← fderiv_productSection_first_apply hk x z v]
      change fderiv ℝ (fun a => k a z) x v = 0
      rw [hzero.fderiv_eq,fderiv_const_apply,zero_apply]
    rw [hd]
    simp only [MulZeroClass.mul_zero]

end RothschildStein.S

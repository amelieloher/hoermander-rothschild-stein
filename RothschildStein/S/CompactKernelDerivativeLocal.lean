-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactKernelDerivative
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter Metric
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P]

/-- Derivative under the kernel integral needs a common compact
support only near the parameter point, rather than for all parameters
(BB p. 78; local weak transfer). -/
theorem fderiv_compactKernelIntegral_apply_of_support_near
    {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    {k : P → (Fin n → ℝ) → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) (uncurry k))
    {h : (Fin n → ℝ) → ℝ} (hh : LocallyIntegrable h volume)
    (x v : P) {r : ℝ} (hr : 0 < r)
    (hks : ∀ a z, a ∈ ball x r → z ∉ K → k a z = 0) :
    fderiv ℝ (fun a => ∫ z, h z * k a z) x v =
      ∫ z, h z * fderiv ℝ (uncurry k) (x,z) (v,0) := by
  let χ : ContDiffBump x := ⟨r/2,r,half_pos hr,half_lt_self hr⟩
  let k' : P → (Fin n → ℝ) → ℝ := fun a z => χ a * k a z
  have hk' : ContDiff ℝ (⊤ : ℕ∞) (uncurry k') :=
    (χ.contDiff.comp contDiff_fst).mul hk
  have hs' : ∀ a z, z ∉ K → k' a z = 0 := by
    intro a z hz
    by_cases ha : a ∈ ball x r
    · change χ a * k a z = 0
      rw [hks a z ha hz,MulZeroClass.mul_zero]
    · have hχ : χ a = 0 := χ.zero_of_le_dist (by
        change r ≤ dist a x
        simpa only [mem_ball,not_lt] using ha)
      change χ a * k a z = 0
      rw [hχ,MulZeroClass.zero_mul]
  have hχ : χ =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := χ.eventuallyEq_one
  have he : (fun a => ∫ z, h z * k' a z) =ᶠ[𝓝 x] (fun a => ∫ z, h z * k a z) := by
    filter_upwards [hχ] with a ha
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    change h z * (χ a * k a z) = h z * k a z
    rw [ha,one_mul]
  rw [← he.fderiv_eq]
  rw [fderiv_compactKernelIntegral_apply hK hk' hs' hh x v]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  have hg : uncurry k' =ᶠ[𝓝 (x,z)] uncurry k := by
    have H := hχ.comp_tendsto (continuous_fst.tendsto (x,z))
    filter_upwards [H] with p hp
    change χ p.1 = 1 at hp
    change χ p.1 * k p.1 p.2 = k p.1 p.2
    rw [hp,one_mul]
  change h z * fderiv ℝ (uncurry k') (x,z) (v,0) = _
  rw [hg.fderiv_eq]

end RothschildStein.S

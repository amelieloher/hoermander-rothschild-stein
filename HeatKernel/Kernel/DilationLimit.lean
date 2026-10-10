-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierPointwise

/-! # Small-time limits from a unit-mass dilation profile

An integrable profile of mass one concentrates at the identity under coordinate dilations.
Dominated convergence gives the pointwise limit against every bounded continuous test.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

open RothschildStein RothschildStein.G2

/-- Unit-mass integrable profiles converge to evaluation after small group dilations. -/
theorem tendsto_integral_dilate_profile {n : ℕ} (G : HomogeneousGroup n)
    {k φ : (Fin n → ℝ) → ℝ} (hk : Integrable k) (hmass : ∫ z, k z = 1)
    (hφ : Continuous φ) {C : ℝ} (hC : ∀ z, ‖φ z‖ ≤ C) (x : Fin n → ℝ) :
    Tendsto (fun r : ℝ => ∫ z, k z * φ (G.mul x (G.dilate r z)))
      (𝓝 0) (𝓝 (φ x)) := by
  have hm (r : ℝ) : AEStronglyMeasurable
      (fun z => k z * φ (G.mul x (G.dilate r z))) volume :=
    hk.aestronglyMeasurable.mul
      (hφ.comp ((continuous_mul G).comp
        (continuous_const.prodMk (continuous_dilate G r)))).aestronglyMeasurable
  have hb (r : ℝ) : ∀ᵐ z ∂volume,
      ‖k z * φ (G.mul x (G.dilate r z))‖ ≤ ‖k z‖ * C := by
    exact Eventually.of_forall fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  have hlim : ∀ᵐ z ∂volume, Tendsto
      (fun r : ℝ => k z * φ (G.mul x (G.dilate r z))) (𝓝 0) (𝓝 (k z * φ x)) := by
    apply Eventually.of_forall
    intro z
    have hd := ((continuous_mul G).comp
      ((continuous_const : Continuous (fun _ : ℝ => x)).prodMk
        (continuous_dilate_parameter G z))).tendsto 0
    change Tendsto (fun r => G.mul x (G.dilate r z)) (𝓝 0)
      (𝓝 (G.mul x (G.dilate 0 z))) at hd
    simp only [zero_dilate, mul_zero] at hd
    exact tendsto_const_nhds.mul ((hφ.tendsto x).comp hd)
  have h := tendsto_integral_filter_of_dominated_convergence (fun z => ‖k z‖ * C)
    (Eventually.of_forall hm) (Eventually.of_forall hb) (hk.norm.mul_const C) hlim
  simpa only [integral_mul_const, hmass, one_mul] using h

/-- The dilation substitution transfers the unit-profile limit to a positive-time kernel. -/
theorem tendsto_kernel_integral_of_dilation {n : ℕ} (G : HomogeneousGroup n)
    (p : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    {k φ : (Fin n → ℝ) → ℝ} (hk : Integrable k) (hmass : ∫ z, k z = 1)
    (hφ : Continuous φ) {C : ℝ} (hC : ∀ z, ‖φ z‖ ≤ C) (x : Fin n → ℝ)
    (hsub : ∀ t, 0 < t → (∫ y, p t x y * φ y) =
      ∫ z, k z * φ (G.mul x (G.dilate (Real.sqrt t) z))) :
    Tendsto (fun t => ∫ y, p t x y * φ y) (𝓝[>] 0) (𝓝 (φ x)) := by
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := (tendsto_integral_dilate_profile G hk hmass hφ hC x).comp hsqrt
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hsub t ht).symm

end HeatKernel

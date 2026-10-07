-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ScaledErrorVanish
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Expanding dilations carry each nonzero point outside every
compact set (BB pp. 251–253). -/
theorem eventually_notMem_dilated_compact (K : Set (Fin N → ℝ))
    (hK : IsCompact K) {x : Fin N → ℝ} (hx : x ≠ 0) :
    ∀ᶠ n : ℕ in atTop, G.dilate ((2 : ℝ) ^ n) x ∉ K := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const R
  simp only [zero_mul] at ht
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  filter_upwards [ht.eventually (gt_mem_nhds hn)] with n hnR
  intro hxK
  have hi : ((2 : ℝ) ^ n)⁻¹ = (1 / 2 : ℝ) ^ n := by rw [← inv_pow]; norm_num
  have H := norm_dilate_le_mul G
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n)
    (pow_le_one₀ (by norm_num) (by norm_num)) (G.dilate ((2 : ℝ) ^ n) x)
  rw [← hi, G2.dilate_inv_dilate G (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))] at H
  have hb := mul_le_mul_of_nonneg_left (hR _ hxK) (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n))
  rw [hi] at H hb
  exact (not_lt_of_ge (H.trans hb)) hnR

/-- Pairing an L1 function against a compact test compressed
towards zero tends to zero. This is the dominated-convergence step used
to eliminate the residual atom (BB (6.6)–(6.8), pp. 251–253). -/
theorem tendsto_integral_shrinking_test_zero
    {γ ψ : (Fin N → ℝ) → ℝ} (hγ : Integrable γ)
    (hψ : Continuous ψ) (hs : HasCompactSupport ψ) :
    Tendsto (fun n : ℕ => ∫ x, γ x * ψ (G.dilate ((2 : ℝ) ^ n) x)) atTop (𝓝 0) := by
  let : NeZero N := ⟨Nat.ne_of_gt G.dimension_pos⟩
  obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hs
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun x => γ x * ψ (G.dilate ((2 : ℝ) ^ n) x)) volume :=
    hγ.aestronglyMeasurable.mul
      ((hψ.comp (G2.contDiff_dilate G ((2 : ℝ) ^ n)).continuous).aestronglyMeasurable)
  have hb (n : ℕ) : ∀ᵐ x ∂volume,
      ‖γ x * ψ (G.dilate ((2 : ℝ) ^ n) x)‖ ≤ ‖γ x‖ * C :=
    Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  have ht : ∀ᵐ x ∂volume, Tendsto
      (fun n : ℕ => γ x * ψ (G.dilate ((2 : ℝ) ^ n) x)) atTop (𝓝 0) := by
    filter_upwards [volume.ae_ne (0 : Fin N → ℝ)] with x hx
    have hz : ∀ᶠ n : ℕ in atTop, γ x * ψ (G.dilate ((2 : ℝ) ^ n) x) = 0 := by
      filter_upwards [eventually_notMem_dilated_compact G (tsupport ψ) hs hx] with n hn
      rw [image_eq_zero_of_notMem_tsupport hn, mul_zero]
    exact tendsto_const_nhds.congr' (hz.mono fun n hn => hn.symm)
  have H := tendsto_integral_filter_of_dominated_convergence (fun x => ‖γ x‖ * C)
    (Eventually.of_forall hm) (Eventually.of_forall hb) (hγ.norm.mul_const C) ht
  simpa only [integral_zero] using H

end RothschildStein.H1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.FieldHomogeneity
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Small positive coordinate dilations are contractions in the
fixed sup-norm carrier (BB pp. 265–266). -/
theorem norm_dilationDifferential_le_one {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖G2.dilationDifferential G t‖ ≤ 1 := by
  apply (G2.dilationDifferential G t).opNorm_le_bound (by norm_num : (0 : ℝ) ≤ 1)
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro j
  change ‖t ^ G.weight j * x j‖ ≤ ‖x‖
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht _)]
  calc
    t ^ G.weight j * ‖x j‖ ≤ 1 * ‖x j‖ :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ ht ht1) (norm_nonneg _)
    _ ≤ ‖x‖ := by simpa only [one_mul] using norm_le_pi_norm x j

/-- Each derivative of a dyadic term is bounded by its
geometric coefficient times the corresponding derivative bound of omega
(BB pp. 265–266). -/
theorem norm_iteratedFDeriv_dyadicTerm_le {ω : (Fin N → ℝ) → ℝ}
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) (k : ℕ) {C c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ x, ‖iteratedFDeriv ℝ k ω x‖ ≤ C) (n : ℕ) (x : Fin N → ℝ) :
    ‖iteratedFDeriv ℝ k
      (fun x => c ^ n • ω (G.dilate ((1 / 2 : ℝ) ^ n) x)) x‖ ≤ c ^ n * C := by
  let L := G2.dilationDifferential G ((1 / 2 : ℝ) ^ n)
  have hL : ‖L‖ ≤ 1 := norm_dilationDifferential_le_one G
    (pow_nonneg (by norm_num) _) (pow_le_one₀ (by norm_num) (by norm_num))
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (ω ∘ L) := hω.comp L.contDiff
  change ‖iteratedFDeriv ℝ k (c ^ n • (ω ∘ L)) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (hsm.of_le (by simp)).contDiffAt,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc _)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hc _)
  rw [L.iteratedFDeriv_comp_right hω x (by simp)]
  apply ((iteratedFDeriv ℝ k ω (L x)).norm_compContinuousLinearMap_le _).trans
  calc
    ‖iteratedFDeriv ℝ k ω (L x)‖ * ∏ _ : Fin k, ‖L‖ ≤
        ‖iteratedFDeriv ℝ k ω (L x)‖ * 1 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [Finset.prod_const_one] using
        (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg L) (fun _ _ => hL))
    _ ≤ C := by simpa only [mul_one] using hbound (L x)

/-- The dyadic correction series of every compact smooth omega
is smooth in all orders. The coefficient c is the actual geometric weight
2^{-(Q-2)} when applying this to the fundamental-solution construction
(BB (6.27)–(6.28), pp. 265–266). -/
theorem contDiff_dyadicSeries {ω : (Fin N → ℝ) → ℝ}
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) (hs : HasCompactSupport ω)
    {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x => ∑' n : ℕ, c ^ n • ω (G.dilate ((1 / 2 : ℝ) ^ n) x)) := by
  choose C hC hbound using fun k => hs.exists_bound_iteratedFDeriv hω k
  let L (n : ℕ) := G2.dilationDifferential G ((1 / 2 : ℝ) ^ n)
  have hL (n : ℕ) : ‖L n‖ ≤ 1 :=
    norm_dilationDifferential_le_one G (pow_nonneg (by norm_num) _)
      (pow_le_one₀ (by norm_num) (by norm_num))
  have hsm (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (ω ∘ L n) := hω.comp (L n).contDiff
  apply contDiff_tsum (v := fun k n => c ^ n * C k)
  · intro n
    change ContDiff ℝ (⊤ : ℕ∞) (c ^ n • (ω ∘ L n))
    exact (hsm n).const_smul (c ^ n)
  · intro k _
    exact (summable_geometric_of_lt_one hc hc1).mul_right (C k)
  · intro k n x _
    exact norm_iteratedFDeriv_dyadicTerm_le G hω k hc (hbound k k le_rfl) n x

end RothschildStein.H1

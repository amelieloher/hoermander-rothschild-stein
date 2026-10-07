-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.RadialMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.G2

private theorem power_image_Ioi {Q : ℕ} (hQ : 0 < Q) :
    (fun r : ℝ => r ^ Q) '' Ioi 0 = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact pow_pos hr Q
  · intro ht
    refine ⟨t ^ ((Q : ℝ)⁻¹), Real.rpow_pos_of_pos ht _, ?_⟩
    exact Real.rpow_inv_natCast_pow ht.le (ne_of_gt hQ)

/-- Radial integration of every nonnegative Borel function follows from dilation-volume scaling: the root pushforward calculation and one-dimensional Jacobian give Q times unit-ball volume (BB Proposition 3.21, pp. 105–106). -/
theorem radial_lintegral_of_volumeScaling {N : ℕ} {G : HomogeneousGroup N}
    (hscale : ∀ r : ℝ, 0 < r → ∀ A : Set (Fin N → ℝ),
      volume ((G.dilate r) '' A) = ENNReal.ofReal (r ^ G.homogeneousDimension) * volume A)
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, g (ν x)) = ENNReal.ofReal (G.homogeneousDimension : ℝ) *
      volume {u : Fin N → ℝ | ν u < 1} *
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (G.homogeneousDimension - 1)) * g r := by
  let Q := G.homogeneousDimension
  let m := volume {u : Fin N → ℝ | ν u < 1}
  have hQ : 0 < Q := by
    unfold Q HomogeneousGroup.homogeneousDimension
    exact Finset.sum_pos (fun j _ => G.weight_pos j)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, G.dimension_pos⟩⟩)
  have hcov : (∫⁻ t in Ioi (0 : ℝ), g (t ^ ((Q : ℝ)⁻¹))) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal ((Q : ℝ) * r ^ (Q - 1)) * g r := by
    have hder : ∀ r ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun r : ℝ => r ^ Q)
        ((Q : ℝ) * r ^ (Q - 1)) (Ioi 0) r := by
      intro r _
      exact (hasDerivAt_pow Q r).hasDerivWithinAt
    have hmono : MonotoneOn (fun r : ℝ => r ^ Q) (Ioi 0) := by
      intro r hr s _ hrs
      exact pow_le_pow_left₀ hr.le hrs Q
    have h := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
      measurableSet_Ioi hder hmono (fun t : ℝ => g (t ^ ((Q : ℝ)⁻¹)))
    rw [power_image_Ioi hQ] at h
    rw [h]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [Real.pow_rpow_inv_natCast hr.le (ne_of_gt hQ)]
  calc
    (∫⁻ x, g (ν x)) = ∫⁻ r, g r ∂Measure.map ν volume :=
      (lintegral_map hg hν.1.measurable).symm
    _ = m * ∫⁻ t in Ioi (0 : ℝ), g (t ^ ((Q : ℝ)⁻¹)) := by
      rw [radial_pushforward_of_volumeScaling hscale hν, lintegral_smul_measure,
        lintegral_map hg (Real.continuous_rpow_const (inv_nonneg.mpr (Nat.cast_nonneg _))).measurable]
      rfl
    _ = m * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal ((Q : ℝ) * r ^ (Q - 1)) * g r := by rw [hcov]
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (Nat.cast_nonneg Q), mul_assoc]
      rw [lintegral_const_mul'' _ (by fun_prop)]
      dsimp only [m, Q]
      ac_rfl

end RothschildStein.G2

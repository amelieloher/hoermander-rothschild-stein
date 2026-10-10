-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.SmoothPoincarePower
public import HeatKernel.Poincare.AverageNormalization

/-! Normalized same-ball Poincaré estimates for functions smooth near closed balls. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- A positive uniform same-ball Poincaré constant applies to every function C¹ on a
neighborhood of the closed horizontal ball, for all finite real exponents p≥1. -/
theorem exists_uniform_horizontalPoincare_average_constant {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {κ p : ℝ} (hκ : 240 < κ) (k : ℕ) (hk : 0 < k)
    (hscale : 2 * κ + 22 ≤ (k : ℝ)) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Fin N → ℝ) (r : ℝ), 0 < r →
      ∀ (u : (Fin N → ℝ) → ℝ) (U : Set (Fin N → ℝ)),
        IsOpen U → closure (horizontalBall (G.horizontalFields hq) x r) ⊆ U →
        ContDiffOn ℝ 1 u U →
        (⨍ y in horizontalBall (G.horizontalFields hq) x r,
          |u y - ⨍ z in horizontalBall (G.horizontalFields hq) x r, u z| ^ p) ^ (1 / p) ≤
          C * r * (⨍ y in horizontalBall (G.horizontalFields hq) x r,
            horizontalGradientNorm (G.horizontalFields hq) u y ^ p) ^ (1 / p) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_horizontalPoincare_power_constant
    G hq hqpos hspan hw hκ k hk hscale hp
  refine ⟨C, hC, ?_⟩
  intro x r hr u U hU hsub hu
  let B := horizontalBall (G.horizontalFields hq) x r
  let m := ⨍ y in B, u y
  let g := fun y => horizontalGradientNorm (G.horizontalFields hq) u y ^ p
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hcompact := isCompact_closure_horizontalBall G hq hqpos hspan hw x hr.le
  have hc : ContinuousOn u (closure B) := hu.continuousOn.mono hsub
  have hui : IntegrableOn u B := (hc.integrableOn_compact hcompact).mono_set subset_closure
  have hosc : IntegrableOn (fun y => |u y - m| ^ p) B :=
    (((Real.continuous_rpow_const hp0.le).comp_continuousOn
      (hc.sub continuousOn_const).abs).integrableOn_compact hcompact).mono_set subset_closure
  have hg : ContinuousOn g U :=
    (Real.continuous_rpow_const hp0.le).comp_continuousOn
      (continuousOn_horizontalGradientNorm (fun i => (G.horizontalFields_contDiff hq i).continuous)
        hU hu)
  have hgi : IntegrableOn g B := ((hg.mono hsub).integrableOn_compact hcompact).mono_set subset_closure
  have hgn : ∀ y, 0 ≤ g y := fun _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hh := hbound (show CarnotPoint G hq hqpos hspan from x) r hr u
    (hu.mono (subset_closure.trans hsub)) hui
  have heq₁ := ofReal_integral_eq_lintegral_ofReal hosc
    (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (abs_nonneg _) p)
  have heq₂ := ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hgn)
  rw [← heq₁, ← heq₂, ← ENNReal.ofReal_mul (by positivity)] at hh
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.rpow_nonneg (mul_nonneg hC.le hr.le) p)
      (integral_nonneg hgn))).mp hh
  have hmass : 0 < (volume.restrict B).real univ := by
    rw [measureReal_restrict_apply_univ]
    exact ENNReal.toReal_pos (volume_horizontalBall_pos G hq hqpos hspan x hr).ne'
      (volume_horizontalBall_lt_top G hq hqpos hspan hw x hr.le).ne
  have havg := average_le_of_integral_le (volume.restrict B) (volume.restrict B)
    hmass (by norm_num : (0 : ℝ) < 1) (by simp) hreal
  simp only [mul_one] at havg
  have hn : 0 ≤ ⨍ y in B, |u y - m| ^ p :=
    average_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) p)
  have hga : 0 ≤ ⨍ y in B, g y := average_nonneg hgn
  have hroot := Real.rpow_le_rpow hn havg (one_div_nonneg.mpr hp0.le)
  rw [Real.mul_rpow (by positivity) hga, one_div,
    Real.rpow_rpow_inv (mul_nonneg hC.le hr.le) hp0.ne'] at hroot
  simpa only [one_div] using hroot

end HeatKernel

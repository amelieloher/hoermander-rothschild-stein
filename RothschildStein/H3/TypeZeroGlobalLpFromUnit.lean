-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroPrincipalValueLocalScaling
public import RothschildStein.H3.GaugeLpExhaustion
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory Set
open scoped ENNReal
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Scaling a unit-ball estimate gives the same bound on every larger ball. -/
theorem TypeZero.principalValue_sublevel_bound_of_unit {ν : G2.HomogeneousNorm G}
    {k : (Fin N → ℝ) → ℝ} (hk : TypeZero G ν k) (p : ℝ≥0∞) (C : ℝ)
    (hunit : ∀ u : (Fin N → ℝ) → ℝ, ContDiff ℝ 1 u → HasCompactSupport u →
      (∀ x, 1 ≤ ν x → u x = 0) →
      eLpNorm (H1.principalValueConvolution G ν k u) p
        (volume.restrict {x | ν x < 1}) ≤ ENNReal.ofReal C * eLpNorm u p volume)
    {u : (Fin N → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u)
    {σ R : ℝ} (hR : 0 < R) (hσR : σ ≤ R) (hsu : ∀ x, σ ≤ ν x → u x = 0) :
    eLpNorm (H1.principalValueConvolution G ν k u) p
      (volume.restrict {x | ν x < R}) ≤ ENNReal.ofReal C * eLpNorm u p volume := by
  have hut : ContDiff ℝ 1 (fun x => u (G.dilate R x)) :=
    hu.comp ((G2.contDiff_dilate G R).of_le (by simp))
  have hst : HasCompactSupport (fun x => u (G.dilate R x)) :=
    hs.comp_homeomorph (G2.dilationHomeomorph G R hR)
  have ht := hunit (fun x => u (G.dilate R x)) hut hst (by
    intro x hx
    apply hsu
    rw [ν.gauge.2.2.2 R hR]
    nlinarith)
  rw [hk.principalValue_eLpNorm_dilate_sublevel G hu hs p 1 hR,
    mul_one, eLpNorm_dilate G u p hR] at ht
  let a : ℝ≥0∞ := ENNReal.ofReal ((R ^ G.homogeneousDimension)⁻¹) ^ (1 / p.toReal)
  have ha0 : a ≠ 0 := (ENNReal.rpow_pos
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hR _))) ENNReal.ofReal_ne_top).ne'
  have hat : a ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hR _))).ne' ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_right ha0 hat).mp
  calc
    a * _ ≤ ENNReal.ofReal C * (a * eLpNorm u p volume) := ht
    _ = a * (ENNReal.ofReal C * eLpNorm u p volume) := by ac_rfl

/-- A unit-ball type-zero bound implies the global compact-source bound
with the same constant, by dilation and gauge exhaustion. -/
theorem TypeZero.principalValue_global_bound_of_unit {ν : G2.HomogeneousNorm G}
    {k : (Fin N → ℝ) → ℝ} (hk : TypeZero G ν k)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) (C : ℝ)
    (hunit : ∀ u : (Fin N → ℝ) → ℝ, ContDiff ℝ 1 u → HasCompactSupport u →
      (∀ x, 1 ≤ ν x → u x = 0) →
      eLpNorm (H1.principalValueConvolution G ν k u) p
        (volume.restrict {x | ν x < 1}) ≤ ENNReal.ofReal C * eLpNorm u p volume)
    {u : (Fin N → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u)
    {σ : ℝ} (hσ : 0 < σ) (hsu : ∀ x, σ ≤ ν x → u x = 0) :
    MemLp (H1.principalValueConvolution G ν k u) p volume ∧
    eLpNorm (H1.principalValueConvolution G ν k u) p volume ≤
      ENNReal.ofReal C * eLpNorm u p volume := by
  apply memLp_of_uniform_sublevel_bounds volume ν _ hp0 hpt
    (hk.continuous_principalValue G hu hs).aestronglyMeasurable
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hu.continuous.memLp_of_hasCompactSupport hs).eLpNorm_lt_top)
  intro n
  have h := hk.principalValue_sublevel_bound_of_unit G p C hunit hu hs
    (R := σ + (n : ℝ) + 1) (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n]) hsu
  apply le_trans (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume ?_)) h
  intro x hx
  change ν x < (n : ℝ) + 1 at hx
  change ν x < σ + (n : ℝ) + 1
  linarith

/-- Compact support supplies the radius needed for the global estimate. -/
theorem TypeZero.principalValue_global_compact_bound_of_unit {ν : G2.HomogeneousNorm G}
    {k : (Fin N → ℝ) → ℝ} (hk : TypeZero G ν k)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) (C : ℝ)
    (hunit : ∀ u : (Fin N → ℝ) → ℝ, ContDiff ℝ 1 u → HasCompactSupport u →
      (∀ x, 1 ≤ ν x → u x = 0) →
      eLpNorm (H1.principalValueConvolution G ν k u) p
        (volume.restrict {x | ν x < 1}) ≤ ENNReal.ofReal C * eLpNorm u p volume)
    {u : (Fin N → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u) :
    MemLp (H1.principalValueConvolution G ν k u) p volume ∧
    eLpNorm (H1.principalValueConvolution G ν k u) p volume ≤
      ENNReal.ofReal C * eLpNorm u p volume := by
  obtain ⟨B, hB⟩ := hs.isCompact.bddAbove_image ν.gauge.1.continuousOn
  apply hk.principalValue_global_bound_of_unit G hp0 hpt C hunit hu hs
    (σ := |B| + 1) (by positivity)
  intro x hx
  by_contra hn
  have hb : ν x ≤ B := hB ⟨x, subset_closure hn, rfl⟩
  have hab := le_abs_self B
  linarith

end RothschildStein.H3

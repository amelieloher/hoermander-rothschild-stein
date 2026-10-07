-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.CZDecomposition
public import RothschildStein.H2.GoodBadCover
public import RothschildStein.H2.FractionalHedberg
public import RothschildStein.H2.MaximalLevelSets
public import RothschildStein.H2.MaximalEndpoint
public import RothschildStein.H2.MaximalWeak
public import RothschildStein.H2.Vitali
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.WithDensity
public import RothschildStein.H2.LpBounds
public import Mathlib.MeasureTheory.Integral.Prod
public import RothschildStein.H2.UniformVolume

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal BigOperators Classical

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Local Calderón–Zygmund decomposition (BB Thm 7.32,
pp. 324–325). The decomposition satisfies the covering, average and overlap bounds, with radii capped by κ/5. The bad pieces have zero integral, finite pointwise support, and total L¹ mass at most twice the input mass. Their L² membership and the good part's L² membership are included. -/
theorem LocDoubling.calderon_zygmund_decomposition_of_volume_lower (D : LocDoubling X) {xbar : X}
    (hxbar : xbar ∈ D.Ω₀) (f : X → ℝ) (hf : IntegrableOn f D.Ω₂ D.μ)
    (hn : ∀ᵐ x ∂D.μ.restrict D.Ω₂, 0 ≤ f x)
    (hsupport : ∀ᵐ y ∂D.μ.restrict D.Ω₂, y ∉ ball xbar D.κ → f y = 0)
    {m : ℝ} (hm : 0 < m)
    (hml : ∀ z ∈ D.Ω₁, ENNReal.ofReal m ≤ D.μ (ball z D.κ))
    {α : ℝ} (hα : 0 < α)
    (hthreshold : eLpNorm f 1 (D.μ.restrict D.Ω₂) / ENNReal.ofReal α < D.μ D.Ω₁) :
    ∃ u : Set X, u.Countable ∧
      let A := goodBadLevelSet D f α
      let B : u → Set X := fun z => ball (z : X) (whitneyRadius A D.κ z)
      (∀ z : u, 0 < whitneyRadius A D.κ z ∧ 5 * whitneyRadius A D.κ z ≤ D.κ) ∧
      (∀ z : u, ball (z : X) (5 * whitneyRadius A D.κ z) ⊆ D.Ω₁) ∧
      (∑' z : u, D.μ (B z)) ≤ ENNReal.ofReal (D.C_D ^ 7 + D.C_D ^ 5) *
        (eLpNorm f 1 (D.μ.restrict D.Ω₂) / ENNReal.ofReal α) ∧
      (∀ x, coverMultiplicity B x ≤ ENNReal.ofReal (D.C_D ^ 7 + D.C_D ^ 5)) ∧
      ∃ g b, CZDecompositionFacts (D.μ.restrict D.Ω₂) B f
        ((D.C_D ^ 7 + D.C_D ^ 5) * goodAverageConstant D m * α) g b := by
  have hfacts := D.good_bad_cover hxbar f hf hsupport hα hm hml hthreshold
  rcases hfacts with ⟨hopen, _, hinside, _, _, u, huA, hu, hcover,
    hgood, havg, hmass, hoverlap, hr, hlarge, hfinite⟩
  let A := goodBadLevelSet D f α
  let r : X → ℝ := whitneyRadius A D.κ
  let B : u → Set X := fun z => ball (z : X) (r z)
  let ν := D.μ.restrict D.Ω₂
  have hCD : 0 ≤ D.C_D := by linarith [D.one_lt_C_D]
  let N := D.C_D ^ 7 + D.C_D ^ 5
  let L := goodAverageConstant D m * α
  let : Countable u := hu.to_subtype
  have hB : ∀ z : u, MeasurableSet (B z) := fun _ => isOpen_ball.measurableSet
  have hBi : ∀ z : u, B z ⊆ D.Ω₂ := fun z =>
    (ball_subset_ball (by linarith [(hr z z.property).1])).trans
      ((hlarge z z.property).trans D.sub₁₂)
  have hνB : ∀ z : u, ν (B z) = D.μ (B z) := fun z => by
    rw [Measure.restrict_apply (hB z), inter_eq_left.mpr (hBi z)]
  have hrestrict : ∀ z : u, ν.restrict (B z) = D.μ.restrict (B z) := fun z =>
    Measure.restrict_restrict_of_subset (hBi z)
  have hv : ∀ z : u, 0 < ν (B z) ∧ ν (B z) < ∞ := by
    intro z
    rw [hνB z]
    have hz : (z : X) ∈ D.Ω₁ := hinside (huA z.property)
    have hv := D.outerPatch.doubling z hz (r z) (hr z z.property).1
      (by change r z ≤ 6 * D.κ; linarith [(hr z z.property).2, D.κ_pos])
    exact ⟨hv.1, hv.2.1⟩
  have hfiniteB : ∀ x, {z : u | x ∈ B z}.Finite := by
    intro x
    apply ((hfinite x).preimage (fun _ _ _ _ h => Subtype.val_injective h)).subset
    intro z hz
    exact ⟨z.property, hz⟩
  have hcount : ∀ x, coverMultiplicity B x ≤ ENNReal.ofReal N := by
    intro x
    calc
      _ = ∑' z : u, if (z : X) ∈ u ∧ x ∈ ball (z : X) (r z) then (1 : ℝ≥0∞) else 0 := by
        apply tsum_congr
        intro z
        simp [B, z.property]
      _ ≤ ∑' z : X, if z ∈ u ∧ x ∈ ball z (r z) then (1 : ℝ≥0∞) else 0 := by
        exact ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun z : u => (z : X)) Subtype.val_injective
          (fun z : X => if z ∈ u ∧ x ∈ ball z (r z) then (1 : ℝ≥0∞) else 0)
      _ ≤ _ := hoverlap x
  have hL : 0 ≤ L := mul_nonneg
    (le_trans (pow_nonneg (by linarith [D.one_lt_C_D]) 6) (le_max_left _ _)) hα.le
  have hN : 1 ≤ N := by
    have hp : 1 ≤ D.C_D ^ 7 := one_le_pow₀ D.one_lt_C_D.le
    have hq : 0 ≤ D.C_D ^ 5 := pow_nonneg (by linarith [D.one_lt_C_D]) _
    dsimp [N]
    linarith
  have hgoodν : ∀ᵐ x ∂ν, x ∉ ⋃ z : u, B z → f x ≤ D.C_D ^ 3 * α := by
    filter_upwards [ae_restrict_of_ae hgood,
      ae_restrict_mem D.open₂.measurableSet, hsupport] with x hx hx₂ hxsp hnot
    by_cases hx₁ : x ∈ D.Ω₁
    · have hxA : x ∉ A := by
        intro hxa
        change x ∈ goodBadLevelSet D f α at hxa
        rw [hcover] at hxa
        obtain ⟨z, hz, hball⟩ := mem_iUnion₂.mp hxa
        exact hnot (mem_iUnion.mpr ⟨⟨z, hz⟩, hball⟩)
      exact (le_abs_self (f x)).trans
        ((ENNReal.ofReal_le_ofReal_iff (mul_nonneg (pow_nonneg hCD 3) hα.le)).mp
          (by simpa only [← Real.norm_eq_abs, ofReal_norm] using hx ⟨hx₁, hxA⟩))
    · have hxball : x ∉ ball xbar D.κ := fun h => hx₁
        (D.incl₀ xbar hxbar (ball_subset_closedBall ((ball_subset_ball (by linarith [D.κ_pos] : D.κ ≤ 6 * D.κ)) h)))
      rw [hxsp hxball]
      exact mul_nonneg (pow_nonneg hCD 3) hα.le
  have havgν : ∀ z : u, (⨍⁻ x in B z, ‖f x‖ₑ ∂ν) ≤ ENNReal.ofReal L := by
    intro z
    rw [setLAverage_eq, hrestrict z, hνB z]
    simpa only [setLAverage_eq] using havg z z.property
  obtain ⟨g, b, hcz⟩ := exists_cz_decomposition ν B hB
    (fun z => (hv z).2.ne) (fun z => (hv z).1.ne') hfiniteB f hf hn
    hL (le_trans zero_le_one hN) havgν hcount hgoodν
  have hcG : D.C_D ^ 3 ≤ goodAverageConstant D m :=
    (pow_le_pow_right₀ D.one_lt_C_D.le (by norm_num : 3 ≤ 6)).trans (le_max_left _ _)
  have hCL : D.C_D ^ 3 * α ≤ N * L := by
    dsimp [L]
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) hL]
  have heq : max (D.C_D ^ 3 * α) (N * L) = N * goodAverageConstant D m * α := by
    rw [max_eq_right hCL]
    dsimp [L]
    ring
  rw [heq] at hcz
  exact ⟨u, hu, (fun z => hr z z.property),
    (fun z => hlarge z z.property), hmass, hcount, g, b, hcz⟩

end RothschildStein.H2

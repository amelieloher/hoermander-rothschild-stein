-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompactCurveExit
public import RothschildStein.H3.ControlCurveBounds
public import RothschildStein.H3.ControlMetric
public import RothschildStein.H2.HolderOperations
public import RothschildStein.G1.DistanceVariation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal
namespace RothschildStein.H3
variable {N q : ℕ} {G : HomogeneousGroup N}

private theorem holder_cross_boundary_of_controlNorm
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : G2.ControlNormConclusion G driftWeight Y) :
    letI := gaugeMetric G H.norm H.constant_one H.symmetric
    ∀ {a : ℝ≥0} {A : Set (ControlCarrier N)} {f : ControlCarrier N → ℝ},
      IsOpen A → HasCompactSupport f → tsupport f ⊆ A →
      H2.holderSemi a A f < ⊤ → ∀ x ∈ A, ∀ y ∉ A,
        |f x - f y| ≤ (H2.holderSemi a A f).toReal * dist x y ^ (a : ℝ) := by
  let : MetricSpace (ControlCarrier N) := gaugeMetric G H.norm H.constant_one H.symmetric
  intro a A f hA hcf hs hsemi x hx y hy
  have hfy : f y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hs h))
  by_cases hfx : f x = 0
  · rw [hfx, hfy, sub_self, abs_zero]; positivity
  have hfinite : controlDistance univ driftWeight Y x y ≠ ⊤ := by
    intro he
    exact ENNReal.ofReal_ne_top ((H.distance_eq x y).symm.trans he)
  have hb : |f x - f y| ≤ (H2.holderSemi a A f).toReal *
      (controlDistance univ driftWeight Y x y).toReal ^ (a : ℝ) := by
    apply G1.variation_le_controlDistance_of_curve_bound hfinite
      (fun δ => (H2.holderSemi a A f).toReal * δ ^ (a : ℝ))
      (continuous_const.mul (Real.continuous_rpow_const a.coe_nonneg))
    · intro r hr s _ hrs
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr hrs a.coe_nonneg)
        ENNReal.toReal_nonneg
    · intro δ γ hγ h0 h1
      have hc : ContinuousOn γ (Icc (0 : ℝ) 1) := by
        simpa only [uIcc_of_le zero_le_one] using hγ.2.1.continuousOn
      obtain ⟨t, ht, hzA, hzK⟩ := exists_curve_point_outside_compact
        (X := ControlCarrier N) hcf.isCompact hA hs hc
        (by simpa only [h0] using subset_tsupport f hfx) (by simpa only [h1] using hy)
      have hfz : f (γ t) = 0 := image_eq_zero_of_notMem_tsupport hzK
      have hd : dist x (γ t) ≤ δ := by
        have hn := controlledCurve_stays_close_of_controlNorm H hγ ht
        have hn' : (controlDistance univ driftWeight Y x (γ t)).toReal ≤ δ := by
          simpa only [h0] using hn
        exact (gaugeMetric_controlDistance G H x (γ t)).trans_le hn'
      calc
        |f x - f y| = |f x - f (γ t)| := by rw [hfy, hfz]
        _ ≤ (H2.holderSemi a A f).toReal * dist x (γ t) ^ (a : ℝ) :=
          H2.sub_le_holderSemi hsemi hx hzA
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow dist_nonneg hd a.coe_nonneg) ENNReal.toReal_nonneg
  exact hb.trans_eq (congrArg
    (fun d : ℝ => (H2.holderSemi a A f).toReal * d ^ (a : ℝ))
    (gaugeMetric_controlDistance G H x y)).symm

/-- Compact support strictly inside an open set permits global Hölder
zero extension without increasing the seminorm. Control curves supply the
boundary point under the global control-metric comparison
(BB Prop. 2.18(iii), pp. 84–86). -/
theorem holderSemi_global_le_of_controlNorm
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : G2.ControlNormConclusion G driftWeight Y) :
    letI := gaugeMetric G H.norm H.constant_one H.symmetric
    ∀ {a : ℝ≥0} {A : Set (ControlCarrier N)} {f : ControlCarrier N → ℝ},
      IsOpen A → HasCompactSupport f → tsupport f ⊆ A →
      H2.holderSemi a univ f ≤ H2.holderSemi a A f := by
  let : MetricSpace (ControlCarrier N) := gaugeMetric G H.norm H.constant_one H.symmetric
  intro a A f hA hcf hs
  by_cases ht : H2.holderSemi a A f = ⊤
  · rw [ht]; exact le_top
  have hsemi := lt_top_iff_ne_top.mpr ht
  have hbound : ∀ x ∈ (univ : Set (ControlCarrier N)), ∀ y ∈ univ,
      |f x - f y| ≤ (H2.holderSemi a A f).toReal * dist x y ^ (a : ℝ) := by
    intro x _ y _
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ A
      · exact H2.sub_le_holderSemi hsemi hx hy
      · exact holder_cross_boundary_of_controlNorm H hA hcf hs hsemi x hx y hy
    · by_cases hy : y ∈ A
      · have hb := holder_cross_boundary_of_controlNorm H hA hcf hs hsemi y hy x hx
        simpa only [abs_sub_comm, dist_comm] using hb
      · have hfx := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
        have hfy := image_eq_zero_of_notMem_tsupport (fun h => hy (hs h))
        rw [hfx, hfy, sub_self, abs_zero]; positivity
  have hb := H2.holderSemi_le_of_bound ENNReal.toReal_nonneg hbound
  simpa only [ENNReal.ofReal_toReal ht] using hb

/-- Both terms of the full bounded Hölder norm have exactly
the same value before and after compactly supported zero extension. -/
theorem boundedHolderNorm_global_eq_of_controlNorm
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : G2.ControlNormConclusion G driftWeight Y) :
    letI := gaugeMetric G H.norm H.constant_one H.symmetric
    ∀ {a : ℝ≥0} {A : Set (ControlCarrier N)} {f : ControlCarrier N → ℝ},
      IsOpen A → HasCompactSupport f → tsupport f ⊆ A →
      H2.boundedHolderNorm a univ f = H2.boundedHolderNorm a A f := by
  let : MetricSpace (ControlCarrier N) := gaugeMetric G H.norm H.constant_one H.symmetric
  intro a A f hA hcf hs
  apply le_antisymm
  · have hsup : H2.holderSup univ f ≤ H2.holderSup A f := by
      apply iSup_le
      intro x
      by_cases hx : x.val ∈ A
      · exact le_iSup (fun y : A => ENNReal.ofReal |f y|) ⟨x.val, hx⟩
      · have hz := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
        simp only [hz, abs_zero, ENNReal.ofReal_zero]
        exact zero_le
    exact add_le_add hsup (holderSemi_global_le_of_controlNorm H hA hcf hs)
  · exact H2.boundedHolderNorm_restrict (subset_univ _)

end RothschildStein.H3

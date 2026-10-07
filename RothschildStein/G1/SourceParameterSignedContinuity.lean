-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SourceParameterFlowContinuity
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped Topology NNReal

namespace RothschildStein.G1

/-- Reverse negative times and the field together to obtain
parameter continuity on a common signed time interval, without
parameter derivatives (BB Props 9.53–9.54, p. 452). -/
theorem flow_solutions_signed_parameter_continuousOn {P E : Type*}
    [UniformSpace P] [LocallyCompactSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set P} (hU : IsOpen U) {K : Set E} (hK : IsCompact K)
    (Z : P × E → E) (hZ : ContinuousOn Z (U ×ˢ K))
    (Φ : P → ℝ → E) {T : ℝ} (hT : 0 ≤ T) {L : ℝ≥0}
    (hLip : ∀ p ∈ U, LipschitzOnWith L (fun y => Z (p, y)) K)
    (hrange : ∀ p ∈ U, ∀ t ∈ Icc (-T) T, Φ p t ∈ K)
    (hode : ∀ p ∈ U, ∀ t ∈ Icc (-T) T, HasDerivAt (Φ p) (Z (p, Φ p t)) t)
    (hinit : ContinuousOn (fun p => Φ p 0) U) :
    ∀ τ ∈ Icc (-T) T, ContinuousOn (fun p => Φ p τ) U := by
  have hpos : Icc (0 : ℝ) T ⊆ Icc (-T) T := Icc_subset_Icc_left (by linarith)
  have hneg : ∀ t ∈ Icc (0 : ℝ) T, -t ∈ Icc (-T) T := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  intro τ hτ
  rcases le_total 0 τ with hτ0 | hτ0
  · exact flow_solutions_parameter_continuousOn hU hK Z hZ Φ hLip
      (fun p hp t ht => hrange p hp t (hpos ht))
      (fun p hp t ht => hode p hp t (hpos ht)) hinit τ ⟨hτ0, hτ.2⟩
  · have hLipneg : ∀ p ∈ U, LipschitzOnWith L (fun y => -Z (p, y)) K := by
      intro p hp
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      simpa only [dist_neg_neg] using (hLip p hp).dist_le_mul x hx y hy
    have hodeneg : ∀ p ∈ U, ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivAt (fun q => Φ p (-q)) (-Z (p, Φ p (-t))) t := by
      intro p hp t ht
      simpa only [Function.comp_def, neg_one_smul] using
        (hode p hp (-t) (hneg t ht)).scomp t (hasDerivAt_neg t)
    have hc := flow_solutions_parameter_continuousOn hU hK (fun q => -Z q) hZ.neg
      (fun p t => Φ p (-t)) hLipneg
      (fun p hp t ht => hrange p hp (-t) (hneg t ht)) hodeneg
      (by simpa only [neg_zero] using hinit) (-τ) ⟨by linarith, by linarith [hτ.1]⟩
    simpa only [neg_neg] using hc

/-- Uniform time speeds combine with signed parameter continuity
to give joint continuity on the complete signed time cylinder. -/
theorem flow_solutions_signed_joint_continuousOn {P E : Type*}
    [UniformSpace P] [LocallyCompactSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set P} (hU : IsOpen U) {K : Set E} (hK : IsCompact K)
    (Z : P × E → E) (hZ : ContinuousOn Z (U ×ˢ K))
    (Φ : P → ℝ → E) {T : ℝ} (hT : 0 ≤ T) {L M : ℝ≥0}
    (hLip : ∀ p ∈ U, LipschitzOnWith L (fun y => Z (p, y)) K)
    (hbound : ∀ p ∈ U, ∀ y ∈ K, ‖Z (p, y)‖ ≤ M)
    (hrange : ∀ p ∈ U, ∀ t ∈ Icc (-T) T, Φ p t ∈ K)
    (hode : ∀ p ∈ U, ∀ t ∈ Icc (-T) T, HasDerivAt (Φ p) (Z (p, Φ p t)) t)
    (hinit : ContinuousOn (fun p => Φ p 0) U) :
    ContinuousOn (fun q : P × ℝ => Φ q.1 q.2) (U ×ˢ Icc (-T) T) := by
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith' _ M
  · intro p hp
    apply (convex_Icc (-T) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => (hode p hp t ht).hasDerivWithinAt)
    intro t ht
    change ‖Z (p, Φ p t)‖ ≤ (M : ℝ)
    exact hbound p hp _ (hrange p hp t ht)
  · exact flow_solutions_signed_parameter_continuousOn hU hK Z hZ Φ hT hLip hrange hode hinit

end RothschildStein.G1

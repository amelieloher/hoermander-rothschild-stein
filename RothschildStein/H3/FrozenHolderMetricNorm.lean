-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ControlMetric
public import RothschildStein.H2.HolderSpaces
public import RothschildStein.S.HolderBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal NNReal
namespace RothschildStein.H3

private theorem metric_holder_candidate_inf_eq {X : Type*} [MetricSpace X]
    (a : ℝ≥0) (V : Set X) (f : X → ℝ) :
    sInf {C : ℝ≥0∞ | C < ⊤ ∧ ∀ x ∈ V, ∀ y ∈ V,
      ENNReal.ofReal |f x - f y| ≤ C * ENNReal.ofReal (dist x y) ^ (a : ℝ)} =
      H2.holderSemi a V f := by
  unfold H2.holderSemi
  apply le_antisymm
  · unfold eHolderNorm
    refine le_iInf fun C => le_iInf fun hC => ?_
    apply sInf_le
    refine ⟨ENNReal.coe_lt_top, ?_⟩
    intro x hx y hy
    simpa only [edist_dist, Real.dist_eq, Subtype.dist_eq] using hC ⟨x, hx⟩ ⟨y, hy⟩
  · apply le_sInf
    intro C hC
    have hh : HolderWith C.toNNReal a (fun x : V => f x) := by
      intro x y
      have hb := hC.2 x x.property y y.property
      rw [← ENNReal.coe_toNNReal hC.1.ne] at hb
      simpa only [edist_dist, Real.dist_eq, Subtype.dist_eq] using hb
    exact hh.eHolderNorm_le.trans_eq (ENNReal.coe_toNNReal hC.1.ne)

/-- The fixed least-constant seminorm agrees exactly with
Mathlib's auxiliary seminorm when the extended distance is the metric
distance. This includes infinite seminorms and arbitrary subsets. -/
theorem frozen_holderSeminorm_eq_metric_semi {N : ℕ}
    (metric : MetricSpace (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (hd : ∀ x y, d x y = ENNReal.ofReal (@dist (Fin N → ℝ) metric.toDist x y))
    (a : ℝ≥0) (V : Set (Fin N → ℝ)) (f : (Fin N → ℝ) → ℝ) :
    holderSeminorm d a V f = @H2.holderSemi (Fin N → ℝ) metric a V f := by
  unfold holderSeminorm
  simp_rw [hd]
  simpa only [ENNReal.ofReal_lt_top, true_implies] using
    (@metric_holder_candidate_inf_eq (Fin N → ℝ) metric a V f)

/-- Exact agreement of the fixed control seminorm and the auxiliary
gauge-metric seminorm under the control-distance identity. -/
theorem frozen_holderSeminorm_eq_control_semi {N m : ℕ}
    (G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (C : G2.ControlNormConclusion G w X)
    (a : ℝ≥0) (V : Set (Fin N → ℝ)) (f : (Fin N → ℝ) → ℝ) :
    holderSeminorm (controlDistance univ w X) a V f =
      @H2.holderSemi (ControlCarrier N) (gaugeMetric G C.norm C.constant_one C.symmetric) a V f := by
  apply frozen_holderSeminorm_eq_metric_semi
  intro x y
  exact C.distance_eq x y

/-- The supremum terms agree as well, giving exact full-norm
agreement for the fixed control distance on any subset. -/
theorem frozen_holderENorm_eq_control_norm {N m : ℕ}
    (G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (C : G2.ControlNormConclusion G w X)
    (a : ℝ≥0) (V : Set (Fin N → ℝ)) (f : (Fin N → ℝ) → ℝ) :
    holderENorm (controlDistance univ w X) a V f =
      @H2.boundedHolderNorm (ControlCarrier N) (gaugeMetric G C.norm C.constant_one C.symmetric) a V f := by
  unfold holderENorm H2.boundedHolderNorm H2.holderSup
  rw [frozen_holderSeminorm_eq_control_semi G w X C a V f]

end RothschildStein.H3

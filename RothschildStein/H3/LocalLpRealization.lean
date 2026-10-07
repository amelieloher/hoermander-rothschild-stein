-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GroupVolumeLower
public import RothschildStein.H2.LocalOperatorFullExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open scoped ENNReal
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The explicit all-exponent norm coefficient on the fixed group
localization setting; its volume input is independent of the centre. -/
def localLpConstant (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (S cT p : ℝ) : ℝ :=
  letI := gaugeMetric G ν h1 hsym
  H2.operatorAllExponentConstant
    (2 * H2.nonnegativeWeakConstant (groupSetting G ν h1 hsym) 1 S cT
      (groupVolumeLower G ν))
    (2 * H2.nonnegativeWeakConstant (groupSetting G ν h1 hsym) 1 S cT
      (groupVolumeLower G ν)) cT p

/-- A fixed local Lp realization follows from the two L2 bounds and
adjointness. Weak endpoint estimates and positive finite ball measure give
the required bounds (BB Theorem 8.22, proof pp. 357–359). -/
theorem local_lp_realization (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) {A S cT p : ℝ}
    (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)] :
    letI := gaugeMetric G ν h1 hsym
    ∀ (K : ControlCarrier N → ControlCarrier N → ℝ)
      (T Ts : Lp ℝ 2 (volume.restrict (ball (0 : ControlCarrier N) 2)) →L[ℝ]
        Lp ℝ 2 (volume.restrict (ball (0 : ControlCarrier N) 2))),
      H2.LocalL2Certificate (groupSetting G ν h1 hsym) 0 2 1 A S cT K T →
      H2.LocalL2Certificate (groupSetting G ν h1 hsym) 0 2 1 A S cT
        (fun x y => K y x) Ts →
      (∀ v w : Lp ℝ 2 (volume.restrict (ball (0 : ControlCarrier N) 2)),
        (∫ x, (T v) x * w x ∂volume.restrict (ball (0 : ControlCarrier N) 2)) =
          ∫ x, v x * (Ts w) x ∂volume.restrict (ball (0 : ControlCarrier N) 2)) →
      ∃ Tp : Lp ℝ (ENNReal.ofReal p) (volume.restrict (ball (0 : ControlCarrier N) 2)) →L[ℝ]
          Lp ℝ (ENNReal.ofReal p) (volume.restrict (ball (0 : ControlCarrier N) 2)),
        ‖Tp‖ ≤ localLpConstant G ν h1 hsym S cT p ∧
        (∀ v : H2.lpL2Intersection (volume.restrict (ball (0 : ControlCarrier N) 2))
            (ENNReal.ofReal p),
          (fun x => (Tp (v : Lp ℝ (ENNReal.ofReal p)
              (volume.restrict (ball (0 : ControlCarrier N) 2)))) x)
            =ᵐ[volume.restrict (ball (0 : ControlCarrier N) 2)]
            fun x => (T (H2.lpL2ToL2 (volume.restrict (ball (0 : ControlCarrier N) 2))
              (ENNReal.ofReal p) v)) x) := by
  let := gaugeMetric G ν h1 hsym
  intro K T Ts hT hTs hadj
  obtain ⟨hm, hml⟩ := groupVolumeLower_spec G ν h1 hsym
  apply (groupSetting G ν h1 hsym).operator_all_lp_extension_of_l2_certificate
    (xbar := 0) (R := 2) (m := groupVolumeLower G ν)
    (by change dist (0 : ControlCarrier N) 0 < 1; simp)
    (by change ball (0 : ControlCarrier N) 2 ⊆ ball 0 19
        exact ball_subset_ball (by norm_num))
    (by change (2 : ℝ) < 3; norm_num) T Ts hT hTs hadj hm hml hp

end RothschildStein.H3

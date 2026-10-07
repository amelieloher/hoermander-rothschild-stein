-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ControlMetric
public import RothschildStein.H2.HolderSpaces
public import RothschildStein.Definitions.holderENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- The fixed seminorm agrees with the abstract seminorm for
the actual control metric. Coordinate-metric specialization is avoided. -/
theorem holderSeminorm_control_eq_of_controlNorm {N m : ℕ} (G : HomogeneousGroup N)
    {w : Fin m → ℕ+} {Y : Fin m → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : G2.ControlNormConclusion G w Y) :
    let metric : MetricSpace (ControlCarrier N) :=
      gaugeMetric G H.norm H.constant_one H.symmetric
    ∀ {α : ℝ≥0} {A : Set (ControlCarrier N)} {f : (Fin N → ℝ) → ℝ},
      @H2.holderSemi (ControlCarrier N) metric α A (fun x => f x) < ⊤ →
      holderSeminorm (controlDistance univ w Y) (α : ℝ) A f =
        @H2.holderSemi (ControlCarrier N) metric α A (fun x => f x) := by
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G H.norm H.constant_one H.symmetric
  dsimp only
  intro α A f hf
  have hd (x y : ControlCarrier N) : controlDistance univ w Y x y = edist x y := by
    rw [H.distance_eq]
    rw [edist_dist]
    rfl
  have hm : MemHolder α (fun x : A => f x.val) := eHolderNorm_lt_top.mp hf
  apply le_antisymm
  · apply sInf_le
    refine ⟨hf, ?_⟩
    intro x hx y hy _
    have he := hm.holderWith (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)
    simpa only [hd, edist_dist, Real.dist_eq, Subtype.dist_eq,
      hm.coe_nnHolderNorm_eq_eHolderNorm, H2.holderSemi] using he
  · apply le_sInf
    intro C hC
    have hh : HolderWith C.toNNReal α (fun x : A => f x.val) := by
      intro x y
      have he := hC.2 x.val x.property y.val y.property (by rw [hd]; exact edist_lt_top _ _)
      simpa only [hd, ENNReal.coe_toNNReal hC.1.ne, edist_dist, Real.dist_eq,
        Subtype.dist_eq] using he
    simpa only [H2.holderSemi, ENNReal.coe_toNNReal hC.1.ne] using hh.eHolderNorm_le

/-- The full fixed norm agrees with the abstract full norm
for the actual control distance, on inputs of finite seminorm. -/
theorem holderENorm_control_eq_of_controlNorm {N m : ℕ} (G : HomogeneousGroup N)
    {w : Fin m → ℕ+} {Y : Fin m → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : G2.ControlNormConclusion G w Y) :
    let metric : MetricSpace (ControlCarrier N) :=
      gaugeMetric G H.norm H.constant_one H.symmetric
    ∀ {α : ℝ≥0} {A : Set (ControlCarrier N)} {f : (Fin N → ℝ) → ℝ},
      @H2.holderSemi (ControlCarrier N) metric α A (fun x => f x) < ⊤ →
      holderENorm (controlDistance univ w Y) (α : ℝ) A f =
        @H2.boundedHolderNorm (ControlCarrier N) metric α A (fun x => f x) := by
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G H.norm H.constant_one H.symmetric
  dsimp only
  intro α A f hf
  rw [holderENorm, holderSeminorm_control_eq_of_controlNorm G H hf]
  rfl

end RothschildStein.H3

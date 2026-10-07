-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderRegularization
public import RothschildStein.H3.ControlMetric
public import RothschildStein.H2.HolderOperations

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal NNReal
namespace RothschildStein.H3
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Positive unit group mollification does not increase the global
supremum, Hölder seminorm, and their sum (BB Theorem 8.52, pp. 381–382). -/
theorem groupRegularize_holderNorm_le
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (φ : G2.GroupMollifier G ν) (α : ℝ≥0)
    {f : ControlCarrier N → ℝ} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    letI _metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
    @H2.BoundedHolder (ControlCarrier N) _metric α univ (f : ControlCarrier N → ℝ) →
      H2.holderSup univ (G2.groupRegularize G φ f ε : ControlCarrier N → ℝ) ≤
        H2.holderSup univ (f : ControlCarrier N → ℝ) ∧
      @H2.holderSemi (ControlCarrier N) _metric α univ (G2.groupRegularize G φ f ε : ControlCarrier N → ℝ) ≤
        @H2.holderSemi (ControlCarrier N) _metric α univ (f : ControlCarrier N → ℝ) ∧
      @H2.boundedHolderNorm (ControlCarrier N) _metric α univ
        (G2.groupRegularize G φ f ε : ControlCarrier N → ℝ) ≤
        @H2.boundedHolderNorm (ControlCarrier N) _metric α univ (f : ControlCarrier N → ℝ) := by
  let _metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
  intro hb
  have hM (x : Fin N → ℝ) : ‖f x‖ ≤
      (H2.holderSup univ (f : ControlCarrier N → ℝ)).toReal := by
    exact H2.abs_le_holderSup hb.parts.1 (mem_univ x)
  have hS : H2.holderSup univ
      (G2.groupRegularize G φ f ε : ControlCarrier N → ℝ) ≤
      H2.holderSup univ (f : ControlCarrier N → ℝ) := by
    apply iSup_le
    intro x
    have hh := G2.norm_groupRegularize_le G φ hf hM hε (x : Fin N → ℝ)
    exact (ENNReal.ofReal_le_ofReal hh).trans_eq
      (ENNReal.ofReal_toReal hb.parts.1.ne)
  have hH (x y : Fin N → ℝ) : |f x - f y| ≤
      (@H2.holderSemi (ControlCarrier N) _metric α univ (f : ControlCarrier N → ℝ)).toReal *
        G2.gaugeDistance G ν x y ^ (α : ℝ) := by
    change |f x - f y| ≤ _ * @dist (ControlCarrier N) _metric.toDist x y ^ (α : ℝ)
    exact H2.sub_le_holderSemi hb.parts.2 (mem_univ (x : ControlCarrier N))
      (mem_univ (y : ControlCarrier N))
  have hA : @H2.holderSemi (ControlCarrier N) _metric α univ
      (G2.groupRegularize G φ f ε) ≤
      @H2.holderSemi (ControlCarrier N) _metric α univ f := by
    have hh := H2.holderSemi_le_of_bound (δ := α) (A := (univ : Set (ControlCarrier N)))
      ENNReal.toReal_nonneg (fun x _ y _ =>
        groupRegularize_holder_bound G ν φ hf hM hH hε x y)
    exact hh.trans_eq (ENNReal.ofReal_toReal hb.parts.2.ne)
  exact ⟨hS, hA, add_le_add hS hA⟩

end RothschildStein.H3

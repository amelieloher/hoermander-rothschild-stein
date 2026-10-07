-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderBoundary
public import RothschildStein.H3.HolderLowerSemicontinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal NNReal
namespace RothschildStein.H3
variable {N q : ℕ} {G : HomogeneousGroup N}

/-- The compact cutoff product has global Hölder norm bounded by the
global cutoff norm times the input's local norm. Boundary zero extension
uses the global control-curve hypotheses (BB pp. 84–86). -/
theorem boundedHolderNorm_cutoff_product_of_controlNorm
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : G2.ControlNormConclusion G driftWeight Y) :
    letI := gaugeMetric G H.norm H.constant_one H.symmetric
    ∀ {a : ℝ≥0} {A : Set (ControlCarrier N)} {g f : ControlCarrier N → ℝ},
      IsOpen A → HasCompactSupport g → tsupport g ⊆ A →
      H2.BoundedHolder a univ g → H2.BoundedHolder a A f →
      H2.boundedHolderNorm a univ (fun x => g x * f x) ≤
        H2.boundedHolderNorm a univ g * H2.boundedHolderNorm a A f := by
  let : MetricSpace (ControlCarrier N) := gaugeMetric G H.norm H.constant_one H.symmetric
  intro a A g f hA hcg hs hg hf
  have hgA : H2.BoundedHolder a A g :=
    (H2.boundedHolderNorm_restrict (subset_univ _)).trans_lt hg
  have hcp : HasCompactSupport (fun x => g x * f x) := hcg.mul_right
  have hsp : tsupport (fun x => g x * f x) ⊆ A := tsupport_mul_subset_left.trans hs
  rw [boundedHolderNorm_global_eq_of_controlNorm H hA hcp hsp]
  apply (H2.boundedHolderNorm_mul_le hgA hf).trans
  gcongr
  exact H2.boundedHolderNorm_restrict (subset_univ _)

end RothschildStein.H3

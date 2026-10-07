-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SmoothPotentialFullHolderBound
public import RothschildStein.H3.FrozenHolderPotentialSolver

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- The fundamental convolution solves the bounded-ball Hölder problem
with the full control-distance norm under the stated analytic and global
control-norm hypotheses. -/
theorem holder_potential_solver_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (φ : G2.GroupMollifier G C.norm)
    {ρ : ℝ} (hρ : 0 < ρ) {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ f : (Fin N → ℝ) → ℝ,
      Continuous f → HasCompactSupport f → tsupport f ⊆ {x | C.norm x < ρ} →
      holderENorm (controlDistance univ driftWeight H.fields) a univ f < ⊤ →
      memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields)
        (quasiballDomain G C.norm 0 ρ) 2 a (G2.groupConvolution G f K) ∧
      hasDistributionEquationWithDrift (quasiballDomain G C.norm 0 ρ) H.fields
        (fun i => (H.fields_smooth G i).contDiffOn)
        (Distribution.ofFun (quasiballDomain G C.norm 0 ρ)
          (G2.groupConvolution G f K) volume (⊤ : ℕ∞)) f ∧
      holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
        (quasiballDomain G C.norm 0 ρ) 2 a (G2.groupConvolution G f K) ≤
        ENNReal.ofReal A * holderENorm (controlDistance univ driftWeight H.fields) a univ f := by
  apply frozen_holder_potential_solver_of_smooth_source_estimates G H K hQ C φ
    (quasiballDomain G C.norm 0 ρ) ha
  intro t ht hta
  exact smooth_potential_full_holder_bound_of_controlNorm G H K hQ C ht
    (lt_of_le_of_lt (show (t : ℝ) ≤ (a : ℝ) from hta) ha1) hρ

end RothschildStein.H3

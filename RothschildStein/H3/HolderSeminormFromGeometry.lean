-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderPositiveConstantAssembly
public import RothschildStein.H3.FundamentalSecondUnitHolder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace RothschildStein.H3

/-- The weight-two seminorm estimate for a source satisfying the stated
distribution equation, under the principal-value Hölder bounds and global
control-norm comparison. -/
theorem seminorm_estimate_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (φ : G2.GroupMollifier G C.norm) (U : Opens (Fin N → ℝ))
    (a : ℝ≥0) (ha : 0 < (a : ℝ))
    (ha1 : (a : ℝ) < 1) :
    ∃ C₁₁ : ℝ, 0 < C₁₁ ∧ ∀ f : (Fin N → ℝ) → ℝ,
      memHolderXCompact driftWeight H.fields (controlDistance univ driftWeight H.fields) U 2 a f →
      ∃ jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ,
        jet [] = (U : Set (Fin N → ℝ)).indicator f ∧
        (∀ I, wordWeight driftWeight I ≤ 2 →
          hasIntrinsicWordDeriv H.fields ⊤ I ((U : Set (Fin N → ℝ)).indicator f) (jet I) ∧
          Continuous (jet I) ∧ HasCompactSupport (jet I)) ∧
        let F := fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x
        memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) ⊤ 0 a F ∧
        hasDistributionEquationWithDrift ⊤ H.fields (fun i => (H.fields_smooth G i).contDiffOn)
          (Distribution.ofFun ⊤ ((U : Set (Fin N → ℝ)).indicator f) volume (⊤ : ℕ∞)) F ∧
        (∑ I ∈ driftSecondWordFamily q,
          holderSeminorm (controlDistance univ driftWeight H.fields) (a : ℝ) univ (jet I)) ≤
          ENNReal.ofReal C₁₁ *
            holderSeminorm (controlDistance univ driftWeight H.fields) (a : ℝ) univ F := by
  obtain ⟨B, hB, hPV⟩ := exists_fundamental_second_unit_PV_holder_bounds_of_controlNorm G H K C ha ha1
  exact seminorm_estimate_with_positive_constant_of_control_PV_bounds
    G H K hQ C φ U a ha B hB hPV

end RothschildStein.H3

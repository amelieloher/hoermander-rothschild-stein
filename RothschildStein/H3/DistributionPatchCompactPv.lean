-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.RelcompactSolverCompactPv
public import RothschildStein.H3.FrozenDriftEquationPatch
public import RothschildStein.H3.CertifiedPatch

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- An arbitrary distributional solution with Lp forcing
has an actual Sobolev representative and forcing certificate on each
interior patch. The particular solution is constructed from PV bounds. -/
theorem distribution_patch_of_compact_principalValue_bounds {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (p r : ℝ≥0∞) [hpFact : Fact (1 ≤ p)] [hrFact : Fact (1 ≤ r)]
    [hpr : ENNReal.HolderConjugate p r] (hpt : p ≠ ∞)
    (M : ℝ) (hM : 0 ≤ M)
    (hLp : ∀ i j : Fin q, ∀ F : (Fin n → ℝ) → ℝ, ContDiff ℝ 1 F → HasCompactSupport F →
      eLpNorm (H1.principalValueConvolution G H.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) F) p volume ≤
          ENNReal.ofReal M * eLpNorm F p volume)
    (Ω V U : Opens (Fin n → ℝ)) (hV : V ≤ Ω)
    (hVK : IsCompact (closure (V : Set (Fin n → ℝ))))
    (hUK : IsCompact (closure (U : Set (Fin n → ℝ))))
    (hUV : closure (U : Set (Fin n → ℝ)) ⊆ V)
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) (g : (Fin n → ℝ) → ℝ)
    (hg : MemLp g p (volume.restrict (V : Set (Fin n → ℝ))))
    (heq : hasDistributionEquationWithDrift Ω H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) T g) :
    ∃ w : (Fin n → ℝ) → ℝ, memSobolevX driftWeight H.fields U 2 p w ∧
      ∃ E : WeakDriftOperatorData H.fields U p w,
        E.operator =ᵐ[volume.restrict (U : Set (Fin n → ℝ))] g ∧
        ∀ ψ : TestFunction U ℝ (⊤ : ℕ∞),
          T (TestFunction.monoCLM ℝ ψ) = ∫ x, ψ x * w x := by
  obtain ⟨_, _, hsolve⟩ := relcompact_solver_of_compact_principalValue_bounds
    G H K hQ ν h1 hsym p r hpt M hM hLp V hVK
  obtain ⟨v, hv, D, hD, _⟩ := hsolve g hg
  exact patch_certified_of_weak_particular_solution G H Ω V U hV hUK hUV
    p (Fact.out : 1 ≤ p) T g v hv D hD
    (fun ψ => patch_adjoint_equation_of_frozen_drift_equation Ω V hV H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) T g heq ψ)

end RothschildStein.H3

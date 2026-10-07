-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FromBoundedBallSolutions
public import RothschildStein.H3.QuasiballSolverCompactPv
public import RothschildStein.H3.SmoothNormFundamentalCompactPv
public import RothschildStein.H3.FrozenGlobalDriftEquationPatch
public import RothschildStein.H3.SecondFamilyBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- Full repaired global regularity of actual Lp PDE solutions
from fundamental PV bounds, horizontal flows, and Sobolev density.
Both the local regularity step and the half-radius estimate are constructed. -/
theorem exists_global_regularity_constant_of_fundamental_compact_lp_flow_and_density {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (p r : ℝ≥0∞) [hpFact : Fact (1 ≤ p)] [hrFact : Fact (1 ≤ r)]
    [hpr : ENNReal.HolderConjugate p r] (hpt : p ≠ ∞)
    (M : ℝ) (hM : 0 ≤ M)
    (hLp : ∀ i j : Fin q, ∀ f : (Fin n → ℝ) → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm (H1.principalValueConvolution G H.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) f) p volume ≤
          ENNReal.ofReal M*eLpNorm f p volume)
    (E : Fin q → ℝ → (Fin n → ℝ))
    (hE : ∀ i, Continuous (E i)) (hE0 : ∀ i, E i 0 = 0)
    (hflow : ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => H.fields i.succ))
    (hdensity : ∀ v, memSobolevX driftWeight H.fields ⊤ 2 p v →
      Nonempty (SobolevWordApproximation driftWeight H.fields p v)) :
    ∃ C : ℝ, 0 < C ∧ ∀ u g : (Fin n → ℝ) → ℝ,
      MemLp u p (volume : Measure (Fin n → ℝ)) → MemLp g p volume →
      hasDistributionEquationWithDrift ⊤ H.fields (fun i => (H.fields_smooth G i).contDiffOn)
        (Distribution.ofFun ⊤ u volume (⊤ : ℕ∞)) g →
      memSobolevX driftWeight H.fields ⊤ 2 p u ∧
        driftSecondWeakENorm H.fields ⊤ p u ≤ ENNReal.ofReal C * eLpNorm g p volume ∧
        sobolevXENorm driftWeight H.fields ⊤ 2 p u ≤
          ENNReal.ofReal C * (eLpNorm u p volume + eLpNorm g p volume) ∧
        (∑ I ∈ (wordFamily driftWeight 2).filter (fun I => wordWeight driftWeight I = 1),
          weakWordENorm H.fields ⊤ I p u) ≤
          ENNReal.ofReal C * (eLpNorm u p volume + eLpNorm g p volume) := by
  classical
  have hp : 1 ≤ p := Fact.out
  obtain ⟨A, hA, hest⟩ := smoothNorm_estimate_of_fundamental_compact_lp_flow_and_density
    G H K hQ p hp hpt M hM hLp E hE hE0 hflow hdensity
  have hsolve (g : (Fin n → ℝ) → ℝ) (hg : MemLp g p volume) (R : ℝ) (_hR : 0 < R) :
      ∃ v : (Fin n → ℝ) → ℝ,
        memSobolevX driftWeight H.fields (quasiballDomain G (G2.smoothNorm G) 0 R) 2 p v ∧
        ∃ D : WeakDriftOperatorData H.fields (quasiballDomain G (G2.smoothNorm G) 0 R) p v,
          D.operator =ᵐ[volume.restrict
            (quasiballDomain G (G2.smoothNorm G) 0 R : Set (Fin n → ℝ))] g :=
    quasiball_solver_of_compact_principalValue_bounds G H K hQ ν h1 hsym
      (G2.smoothNorm G) R p r hpt M hM hLp g (hg.restrict _)
  obtain ⟨C, hC, hglobal⟩ := exists_global_regularity_constant_of_bounded_ball_solutions G H (G2.smoothNorm G)
    (G2.smoothNorm_smooth G) E hE hE0 hflow p hp hpt hdensity A hA.le hest hsolve
  let Cstar : ℝ := C + (driftSecondWordFamily q).card * A
  have hCA : 0 ≤ ((driftSecondWordFamily q).card : ℝ) * A :=
    mul_nonneg (Nat.cast_nonneg _) hA.le
  have hCstar : 0 < Cstar := by dsimp only [Cstar]; linarith
  have hCC : C ≤ Cstar := le_add_of_nonneg_right hCA
  have hAC : ((driftSecondWordFamily q).card : ℝ) * A ≤ Cstar :=
    le_add_of_nonneg_left hC.le
  refine ⟨Cstar, hCstar, ?_⟩
  intro u g hu hg heq
  have hlocalEq (R : ℝ) (_hR : 0 < R)
      (ψ : TestFunction (quasiballDomain G (G2.smoothNorm G) 0 R) ℝ (⊤ : ℕ∞)) :=
    local_adjoint_equation_of_global_frozen_drift_equation H.fields (H.fields_smooth G)
      u g heq (quasiballDomain G (G2.smoothNorm G) 0 R) ψ
  have hlocal := global_regularity_local_data_of_bounded_ball_solutions G H (G2.smoothNorm G)
    p hp u g hu (hsolve g hg) hlocalEq
  obtain ⟨huS, hnorm⟩ := hglobal u g hu hg hlocalEq
  have hsecond := global_regularity_second_family_bound_of_halfRadius G (G2.smoothNorm G) H.fields
    hp hpt A hA.le hest hu hg hlocal
  have hnormStar := hnorm.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hCC) le_rfl)
  have hfirst : (∑ I ∈ (wordFamily driftWeight 2).filter (fun I => wordWeight driftWeight I = 1),
      weakWordENorm H.fields ⊤ I p u) ≤ sobolevXENorm driftWeight H.fields ⊤ 2 p u := by
    unfold sobolevXENorm
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => bot_le)
  exact ⟨huS, hsecond.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hAC) le_rfl),
    hnormStar, hfirst.trans hnormStar⟩

end RothschildStein.H3

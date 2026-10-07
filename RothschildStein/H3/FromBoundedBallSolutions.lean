-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.UniformGlobalRegularity
public import RothschildStein.H3.LocalDataFromSolutions

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- Uniform global regularity of actual Lp distributional
solutions, from bounded-ball solvability and the proved flow/density
and half-radius inputs. Local Sobolev regularity is constructed. -/
theorem exists_global_regularity_constant_of_bounded_ball_solutions {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (E : Fin q → ℝ → (Fin n → ℝ)) (hE : ∀ i, Continuous (E i))
    (hE0 : ∀ i, E i 0 = 0)
    (hflow : ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => H.fields i.succ))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hdensity : ∀ u, memSobolevX driftWeight H.fields ⊤ 2 p u →
      Nonempty (SobolevWordApproximation driftWeight H.fields p u))
    (K : ℝ) (hK : 0 ≤ K) (hest : HalfRadiusEstimate G ν H.fields p K)
    (hsolve : ∀ g : (Fin n → ℝ) → ℝ, MemLp g p (volume : Measure (Fin n → ℝ)) →
      ∀ R : ℝ, 0 < R → ∃ v : (Fin n → ℝ) → ℝ,
        memSobolevX driftWeight H.fields (quasiballDomain G ν 0 R) 2 p v ∧
        ∃ D : WeakDriftOperatorData H.fields (quasiballDomain G ν 0 R) p v,
          D.operator =ᵐ[volume.restrict (quasiballDomain G ν 0 R : Set (Fin n → ℝ))] g) :
    ∃ C : ℝ, 0 < C ∧ ∀ u g : (Fin n → ℝ) → ℝ,
      MemLp u p (volume : Measure (Fin n → ℝ)) → MemLp g p volume →
      (∀ R : ℝ, 0 < R → ∀ ψ : TestFunction (quasiballDomain G ν 0 R) ℝ (⊤ : ℕ∞),
        Distribution.ofFun ⊤ u volume (⊤ : ℕ∞)
          (TestFunction.monoCLM ℝ
            (Distribution.adjointTest (quasiballDomain G ν 0 R) H.fields (fun _ => 0)
              (fun i => (H.fields_smooth G i).contDiffOn) (by fun_prop) ψ)) =
          Distribution.ofFun (quasiballDomain G ν 0 R) g volume (⊤ : ℕ∞) ψ) →
      memSobolevX driftWeight H.fields ⊤ 2 p u ∧
        sobolevXENorm driftWeight H.fields ⊤ 2 p u ≤
          ENNReal.ofReal C * (eLpNorm u p volume + eLpNorm g p volume) := by
  obtain ⟨C, hC, hglobal⟩ := exists_global_regularity_constant_of_flow_density_and_halfRadius
    G H ν hν E hE hE0 hflow p hp hpt hdensity K hK hest
  refine ⟨C, hC, ?_⟩
  intro u g hu hg heq
  exact hglobal u g hu hg
    (global_regularity_local_data_of_bounded_ball_solutions G H ν p hp u g hu (hsolve g hg) heq)

end RothschildStein.H3

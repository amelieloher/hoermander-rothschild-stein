-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.GaugeFiberData
public import RothschildStein.L1.ModelDataConstruction
public import RothschildStein.L1.FiberTestTransfer
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import RothschildStein.P2.CutoffsHomogeneous
public import RothschildStein.P1.WeightedPoleNormedTarget
public import RothschildStein.P2.CutoffsJets
public import RothschildStein.P1.WeightedTaylorParameters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein.L1

/-- Assemble the fixed lift, proved concrete model, canonical
approximation/densities and fixed-patch geometry. Fiber averaging is
constructed from the coordinate data rather than supplied as another premise
(BB pp. 483–485, 514–520, 608–610). -/
def liftedChartOfData {n k s m : ℕ} {w : Fin k → ℕ+}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (L : FixedLiftData w s Ω X x₀ m) (M : ModelData k s (n+m) w)
    (A : CoordinateApproximationData L M) (H : GaugeFiberData A) :
    P1.LiftedChart w s Ω hΩ X x₀ m :=
  {
    P := L.P
    U := A.U
    G := M.G
    B := M.B
    v := M.v
    Y := M.Y
    Θ := A.Θ
    e := A.e
    R := A.R
    c := A.c
    ωp := A.ωp
    ωm := A.ωm
    vars_lt := L.vars_lt
    isOpen_U := A.isOpen_U
    isCompact_closure_U := A.isCompact_closure_U
    closure_U_subset := fun ξ hξ => L.subset_domain (A.closure_subset_lift hξ)
    center_mem := A.center_mem
    lift_smooth := L.smooth
    lift_free := fun ξ hξ => L.free_spanning ξ (A.closure_subset_lift (subset_closure hξ))
    basis_weight := M.basis_weight
    basis_independent := M.basis_independent
    basis_span := M.basis_span
    generator_coords := M.generator_coords
    inv_eq_neg := M.inv_eq_neg
    model_field_eq := M.model_field_eq
    model_field_smooth := M.model_field_smooth
    model_field_invariant := M.model_field_invariant
    model_field_homogeneous := M.model_field_homogeneous
    model_free := M.model_free
    model_nilpotent := M.model_nilpotent
    model_basis_origin := M.model_basis_origin
    model_exponential := M.model_exponential
    theta_smooth := A.theta_smooth
    chart := A.chart
    radial_curve := A.radial_curve
    theta_antisymm := A.theta_antisymm
    isOpen_T := A.isOpen_T
    remainder_smooth := A.remainder_smooth
    remainder_weight := A.remainder_weight
    remainder_origin := A.remainder_origin
    bracket_approx := A.bracket_approx
    density_smooth := A.density_smooth
    density_pos := A.density_pos
    ωp_smooth := A.ωp_smooth
    ωm_smooth := A.ωm_smooth
    ω_origin := A.ω_origin
    ωm_eq := A.ωm_eq
    jacobian := A.jacobian
    density_bounds := A.density_bounds
    gauge_comparison := H.gauge_comparison
    fiber_average := by
      intro V hV
      have hp : (V : Set (Fin (n+m) → ℝ)) ⊆ basePoint ⁻¹' Ω := by
        intro ξ hξ
        rw [hV] at hξ
        exact L.subset_domain (A.closure_subset_lift (subset_closure hξ))
      exact ⟨fiberTestCLM ⟨Ω,hΩ⟩ V hp, P1.paddingFiberTestCLM_apply ⟨Ω,hΩ⟩ V hp⟩
    ball_bounds := H.ball_bounds
 }

end RothschildStein.L1

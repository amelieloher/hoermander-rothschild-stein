-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.ModelCoordinateData
public import RothschildStein.L1.CanonicalFullTargetRadial
public import RothschildStein.L1.CanonicalTargetDomainOpen
public import RothschildStein.L1.CanonicalChartSmallPatch
public import RothschildStein.L1.CanonicalFrozenDensity
public import RothschildStein.L1.CanonicalVectorApproximation

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- Coordinate data on the fixed free patch retains ambient radial
trajectories when inserted into the actual triangular lift record. -/
def coordinateApproximationDataOfModel {n k s m : ℕ} {w : Fin k → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} (L : FixedLiftData w s Ω X x₀ m)
    (M : ModelData k s (n+m) w)
    (A : ModelCoordinateData (L.U : Set _) (triangularLift X L.P)
      (joinPoint x₀ (0 : Fin m → ℝ)) M) : CoordinateApproximationData L M where
  U := A.U
  isOpen_U := A.isOpen_U
  isCompact_closure_U := A.isCompact_closure_U
  closure_subset_lift := A.closure_subset_domain
  center_mem := A.center_mem
  Θ := A.Θ
  e := A.e
  R := A.R
  c := A.c
  ωp := A.ωp
  ωm := A.ωm
  theta_smooth := A.theta_smooth
  chart := A.chart
  radial_curve := by
    intro η hη u hu
    obtain ⟨γ,h0,h1,hγ⟩ := A.radial_curve η hη u hu
    exact ⟨γ,h0,h1,fun t ht => ⟨L.subset_domain (hγ t ht).1,(hγ t ht).2⟩⟩
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

end RothschildStein.L1

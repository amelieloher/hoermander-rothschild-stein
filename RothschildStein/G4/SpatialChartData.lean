-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ChartAnalyticData
public import RothschildStein.G4.Suboptimality
public import RothschildStein.G4.ChartConstantEnlargement

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators Topology
namespace RothschildStein.G4

/-- Actual local flow charts, with a spatial domain and positive radii.
Finite covers select these same maps, including their ODE trajectories. -/
structure SpatialChartData {P : Type*} {m n : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (Z : P → Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (t : ℝ) where
  U : Set (Fin n → ℝ)
  isOpen_U : IsOpen U
  subset_domain : U ⊆ Ω
  δ : ℝ
  δ_pos : 0 < δ
  c : ℝ
  r₀ : ℝ
  D : ℝ
  κ : ℝ
  c_pos : 0 < c
  c_le_one : c ≤ 1
  radius_pos : 0 < r₀
  radius_le_one : r₀ ≤ 1
  D_pos : 0 < D
  κ_pos : 0 < κ
  κ_small : (n : ℝ) * κ ≤ 1 / 4
  Φ : P → (Fin n → Fin m) →
    (((Fin (n + m) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ)
  smooth : ∀ p B, ContDiffOn ℝ (⊤ : ℕ∞) (Φ p B)
    ((ball 0 δ ×ˢ U) ×ˢ Ioo (-2) 2)
  flow : ∀ p B, ∀ a ∈ ball 0 δ, ∀ x ∈ U,
    Φ p B ((a,x),0) = x ∧ ∀ τ ∈ Ioo (-2 : ℝ) 2,
      Φ p B ((a,x),τ) ∈ Ω ∧
      HasDerivAt (fun v => Φ p B ((a,x),v))
        (∑ j, a j • Z p (Fin.addCases B id j) (Φ p B ((a,x),τ))) τ
  charts : ∀ p, ∀ x ∈ U, ∀ r : ℝ, 0 < r → r ≤ r₀ →
    ∀ B, IsSuboptimal (Z p) w B x t r → ∀ v ∈ weightedBox w (c*r),
    let F := fun u => Φ p B ((Fin.append u v,x),1)
    let Γ := fun u τ => Φ p B ((Fin.append u v,x),τ)
    InjOn F (weightedBox (w ∘ B) (c*r)) ∧
    ChartAnalyticBounds Ω w (Z p) B F (weightedBox (w ∘ B) (c*r)) r κ D ∧
    ChartTrajectories Ω (Z p) B F (weightedBox (w ∘ B) (c*r)) x v Γ ∧
    (v = 0 → F 0 = x) ∧
    ∀ u ∈ weightedBox (w ∘ B) (c*r),
      |frameDet (Z p) B x|/4 ≤ |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ∧
      |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ≤ 4*|frameDet (Z p) B x|

end RothschildStein.G4

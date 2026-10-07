-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FixedLiftData
public import RothschildStein.L1.ModelData

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein.L1

/-- The canonical coordinates, weighted approximation and
corrected endpoint densities on one smaller patch, for the already fixed
lift and common-basis model (BB pp. 483–485, 509–511, 584–585).
The common-source chart and full-target radial clause retain the required
chart-strength bounds. This record makes no existence claim.
The geometry and test map are separate outputs, not fields of this record. -/
structure CoordinateApproximationData {n k s m : ℕ} {w : Fin k → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} (L : FixedLiftData w s Ω X x₀ m) (M : ModelData k s (n+m) w) where
  U : Set (Fin (n+m) → ℝ)
  isOpen_U : IsOpen U
  isCompact_closure_U : IsCompact (closure U)
  closure_subset_lift : closure U ⊆ (L.U : Set (Fin (n+m) → ℝ))
  center_mem : joinPoint x₀ (0 : Fin m → ℝ) ∈ U
  Θ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ)
  e : (Fin (n+m) → ℝ) → OpenPartialHomeomorph (Fin (n+m) → ℝ) (Fin (n+m) → ℝ)
  R : List (Fin k) → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ)
  c : (Fin (n+m) → ℝ) → ℝ
  ωp : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ
  ωm : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ
  theta_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => Θ z.1 z.2) (U ×ˢ U)
  chart : ∀ η ∈ U, (e η).source = U ∧
    (∀ ξ ∈ U, e η ξ = Θ η ξ) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (e η) (e η).source ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (e η).symm (e η).target ∧ Θ η η = 0
  radial_curve : ∀ η ∈ U, ∀ u ∈ (e η).target,
    ∃ γ : ℝ → (Fin (n + m) → ℝ), γ 0 = η ∧ γ 1 = (e η).symm u ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} ∧
        HasDerivAt γ (∑ j, u j • wordBracket (triangularLift X L.P) (M.B j) (γ t)) t)
  theta_antisymm : ∀ η ∈ U, ∀ ξ ∈ U, Θ ξ η = -Θ η ξ
  isOpen_T : IsOpen {z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) |
    z.1 ∈ U ∧ z.2 ∈ (e z.1).target}
  remainder_smooth : ∀ I, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => R I z.1 z.2)
    {z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) | z.1 ∈ U ∧ z.2 ∈ (e z.1).target}
  remainder_weight : ∀ I, I ≠ [] → ∀ η ∈ U,
    WeightedJet M.G.weight (1 - (wordWeight w I : ℤ)) (R I η)
  remainder_origin : ∀ I, I ≠ [] → wordWeight w I ≤ s → ∀ η ∈ U, R I η 0 = 0
  bracket_approx : ∀ I, I ≠ [] → ∀ η ∈ U, ∀ ξ ∈ U,
    fderiv ℝ (Θ η) ξ (wordBracket (triangularLift X L.P) I ξ) =
      wordBracket M.Y I (Θ η ξ) + R I η (Θ η ξ)
  density_smooth : ContDiffOn ℝ (⊤ : ℕ∞) c U
  density_pos : ∀ η ∈ U, 0 < c η
  ωp_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ωp z.1 z.2)
    {z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) | z.1 ∈ U ∧ z.2 ∈ (e z.1).target}
  ωm_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ωm z.1 z.2)
    {z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) | z.1 ∈ U ∧ z.2 ∈ (e z.1).target}
  ω_origin : ∀ η ∈ U, ωp η 0 = 0 ∧ ωm η 0 = 0
  ωm_eq : ∀ η ∈ U, ∀ u, ωm η u = ωp η (-u)
  jacobian : ∀ η ∈ U, ∀ ξ ∈ U,
    0 < 1 + ωp η (Θ η ξ) ∧ 0 < 1 + ωm ξ (Θ η ξ) ∧
    absoluteJacobian (Θ η) ξ = (c η * (1 + ωp η (Θ η ξ)))⁻¹ ∧
    absoluteJacobian (fun ζ => Θ ζ ξ) η = (c ξ * (1 + ωm ξ (Θ η ξ)))⁻¹
  density_bounds : ∀ K : Set (Fin (n + m) → ℝ), IsCompact K → K ⊆ U →
    ∃ cmin cmax C r : ℝ, 0 < cmin ∧ 0 < cmax ∧ 0 < C ∧ 0 < r ∧
      (∀ η ∈ K, cmin ≤ c η ∧ c η ≤ cmax) ∧
      (∀ η ∈ K, ∀ u ∈ (e η).target, ‖u‖ < r →
        |ωp η u| ≤ C * ‖u‖ ∧ |ωm η u| ≤ C * ‖u‖)

end RothschildStein.L1

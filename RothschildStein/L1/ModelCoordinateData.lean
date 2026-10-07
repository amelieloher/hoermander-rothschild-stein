-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CoordinateApproximationData
public import RothschildStein.L1.ModelDataConstruction

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein.L1

/-- Coordinate data with uniform strength on an arbitrary free carrier,
independent of the subsequent triangular splitting. -/
structure ModelCoordinateData {N k s : ℕ} {w : Fin k → ℕ+}
    (V : Set (Fin N → ℝ)) (X : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) (M : ModelData k s N w) where
  U : Set (Fin N → ℝ)
  isOpen_U : IsOpen U
  isCompact_closure_U : IsCompact (closure U)
  closure_subset_domain : closure U ⊆ V
  center_mem : x ∈ U
  Θ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ)
  e : (Fin N → ℝ) → OpenPartialHomeomorph (Fin N → ℝ) (Fin N → ℝ)
  R : List (Fin k) → (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ)
  c : (Fin N → ℝ) → ℝ
  ωp : (Fin N → ℝ) → (Fin N → ℝ) → ℝ
  ωm : (Fin N → ℝ) → (Fin N → ℝ) → ℝ
  theta_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => Θ z.1 z.2) (U ×ˢ U)
  chart : ∀ η ∈ U, (e η).source = U ∧
    (∀ ξ ∈ U, e η ξ = Θ η ξ) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (e η) (e η).source ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (e η).symm (e η).target ∧ Θ η η = 0
  radial_curve : ∀ η ∈ U, ∀ u ∈ (e η).target,
    ∃ γ : ℝ → (Fin N → ℝ), γ 0 = η ∧ γ 1 = (e η).symm u ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ V ∧
        HasDerivAt γ (∑ j, u j • wordBracket X (M.B j) (γ t)) t)
  theta_antisymm : ∀ η ∈ U, ∀ ξ ∈ U, Θ ξ η = -Θ η ξ
  isOpen_T : IsOpen {z : (Fin N → ℝ) × (Fin N → ℝ) |
    z.1 ∈ U ∧ z.2 ∈ (e z.1).target}
  remainder_smooth : ∀ I, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => R I z.1 z.2)
    {z : (Fin N → ℝ) × (Fin N → ℝ) | z.1 ∈ U ∧ z.2 ∈ (e z.1).target}
  remainder_weight : ∀ I, I ≠ [] → ∀ η ∈ U,
    WeightedJet M.G.weight (1 - (wordWeight w I : ℤ)) (R I η)
  remainder_origin : ∀ I, I ≠ [] → wordWeight w I ≤ s → ∀ η ∈ U, R I η 0 = 0
  bracket_approx : ∀ I, I ≠ [] → ∀ η ∈ U, ∀ ξ ∈ U,
    fderiv ℝ (Θ η) ξ (wordBracket X I ξ) =
      wordBracket M.Y I (Θ η ξ) + R I η (Θ η ξ)
  density_smooth : ContDiffOn ℝ (⊤ : ℕ∞) c U
  density_pos : ∀ η ∈ U, 0 < c η
  ωp_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ωp z.1 z.2)
    {z : (Fin N → ℝ) × (Fin N → ℝ) | z.1 ∈ U ∧ z.2 ∈ (e z.1).target}
  ωm_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ωm z.1 z.2)
    {z : (Fin N → ℝ) × (Fin N → ℝ) | z.1 ∈ U ∧ z.2 ∈ (e z.1).target}
  ω_origin : ∀ η ∈ U, ωp η 0 = 0 ∧ ωm η 0 = 0
  ωm_eq : ∀ η ∈ U, ∀ u, ωm η u = ωp η (-u)
  jacobian : ∀ η ∈ U, ∀ ξ ∈ U,
    0 < 1 + ωp η (Θ η ξ) ∧ 0 < 1 + ωm ξ (Θ η ξ) ∧
    absoluteJacobian (Θ η) ξ = (c η * (1 + ωp η (Θ η ξ)))⁻¹ ∧
    absoluteJacobian (fun ζ => Θ ζ ξ) η = (c ξ * (1 + ωm ξ (Θ η ξ)))⁻¹
  density_bounds : ∀ K : Set (Fin N → ℝ), IsCompact K → K ⊆ U →
    ∃ cmin cmax C r : ℝ, 0 < cmin ∧ 0 < cmax ∧ 0 < C ∧ 0 < r ∧
      (∀ η ∈ K, cmin ≤ c η ∧ c η ≤ cmax) ∧
      (∀ η ∈ K, ∀ u ∈ (e η).target, ‖u‖ < r →
        |ωp η u| ≤ C * ‖u‖ ∧ |ωm η u| ≤ C * ‖u‖)


end RothschildStein.L1

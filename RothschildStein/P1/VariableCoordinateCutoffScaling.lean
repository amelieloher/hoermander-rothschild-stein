-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.VariableFieldCutoffScaling
public import RothschildStein.G2.PartialDilation
public import RothschildStein.G2.CoordinateIntegration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open MeasureTheory Filter
namespace RothschildStein.P1
variable {N : ℕ}

/-- Exact coordinate cutoff scaling with an
arbitrary coefficient. The coefficient is evaluated at the rescaled
point; no homogeneity of that coefficient is used. -/
theorem integral_variableCoordinateCutoff_dilate (G : HomogeneousGroup N)
    (j : Fin N) (a β : ℝ)
    (Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hhom : ∀ ξ η, ∀ t : ℝ, 0 < t → ∀ u, u ≠ 0 →
      Ψ ξ η (G.dilate t u) = t ^ β * Ψ ξ η u)
    (p : (Fin N → ℝ) → (Fin N → ℝ) × (Fin N → ℝ))
    (R φ : (Fin N → ℝ) → ℝ) {θ : (Fin N → ℝ) → ℝ}
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) {ε : ℝ} (hε : 0 < ε) :
    (∫ u, Ψ (p u).1 (p u).2 u * R u *
      fderiv ℝ (θ ∘ G.dilate ε⁻¹) u (Pi.single j 1) * φ u) =
      ε ^ (β + (G.homogeneousDimension : ℝ) - a) *
        ∫ v, Ψ (p (G.dilate ε v)).1 (p (G.dilate ε v)).2 v *
          (ε ^ (a - G.weight j) * R (G.dilate ε v)) *
            fderiv ℝ θ v (Pi.single j 1) * φ (G.dilate ε v) := by
  have hY : G2.IsHomogeneousField G (G2.coordinateFields j) (G.weight j : ℝ) := by
    intro t _ _
    change G.dilate t (Hormander.Interface.basisVec j) =
      t ^ (G.weight j : ℝ) • Hormander.Interface.basisVec j
    rw [← G2.dilationDifferential_apply, G2.dilationDifferential_basis, Real.rpow_natCast]
  have he := integral_variableFieldCutoff_dilate G hY Ψ hhom p
    (φ := fun u => R u * φ u) hθ hε
  have hp : ε ^ (β + (G.homogeneousDimension : ℝ) - G.weight j) =
      ε ^ (β + (G.homogeneousDimension : ℝ) - a) * ε ^ (a - G.weight j) := by
    rw [← Real.rpow_add hε]
    congr 1
    ring
  calc
    _ = ∫ u, Ψ (p u).1 (p u).2 u * fieldDerivative (G2.coordinateFields j)
        (θ ∘ G.dilate ε⁻¹) u * (R u * φ u) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun u => by
        dsimp only [fieldDerivative, G2.coordinateFields, Hormander.Interface.basisVec]
        ring)
    _ = _ := he
    _ = _ := by
      rw [hp, mul_assoc, ← integral_const_mul]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall (fun u => by
        dsimp only [fieldDerivative, G2.coordinateFields, Hormander.Interface.basisVec]
        ring)

end RothschildStein.P1

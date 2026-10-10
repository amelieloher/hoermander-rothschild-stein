-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueCylinderScalingGeometry
public import HeatKernel.Moser.MeanValueNormScaling
public import HeatKernel.Moser.MeanValueCoefficientScaling
public import HeatKernel.Moser.MeanValueSignedMatrixPositivePowers
import Mathlib.Tactic

/-! # Essential positive-power mean values on arbitrary horizontal cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- The open-top unit estimate transfers to every horizontal cylinder with its
exact parabolic Jacobian. The constant is independent of the center, radius and
solution. No continuity or preliminary local boundedness is assumed. The
constant may depend on the fixed positive exponent. -/
theorem exists_uniform_matrix_cylinder_positive_power_bound {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν p : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν) (hp : 0 < p)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ), 0 < r →
      ∀ (v : ℝ × (Fin N → ℝ) → ℝ)
      (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ),
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume.restrict
        (Ioo (t₀ - r ^ 2) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ r), 0 ≤ v z) →
      IsLocalWeakSolution G hq hqpos hw hspan
        coeff
        ⟨Ioo (t₀ - r ^ 2) t₀, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x₀ r,
          isOpen_horizontalBall G hq hqpos hspan x₀ r⟩ (fun t x => v (t, x)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      eLpNormEssSup v (volume.restrict
        (Ioo (t₀ - r ^ 2 / 2) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ (r / 2))) ≤
        ENNReal.ofReal C * (ENNReal.ofReal ((r ^ (G.homogeneousDimension + 2))⁻¹) ^ (1 / p) *
          eLpNorm v (ENNReal.ofReal p) (volume.restrict
            (Ioo (t₀ - r ^ 2) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ r))) := by
  obtain ⟨C, hC, hmean⟩ := exists_uniform_signed_matrix_cylinder_positive_power_bound
    G hq hqpos hspan hw hν hp ell upper hell hupper
  refine ⟨C, hC, ?_⟩
  intro t₀ x₀ r hr v coeff _hv0 hweak ha hbound
  exact hmean t₀ x₀ r hr v coeff hweak ha hbound

end HeatKernel

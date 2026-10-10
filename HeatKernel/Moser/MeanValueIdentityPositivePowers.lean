-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueIdentityCoefficients
public import HeatKernel.Bridge.ParabolicValueIntegrability
public import HeatKernel.Kernel.CompactCylinderBounds
public import HeatKernel.Moser.MeanValueCylinderScalingGeometry
public import HeatKernel.Moser.MeanValueNormScaling
public import HeatKernel.Moser.MeanValueMatrixPositivePowers
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
theorem exists_uniform_identity_cylinder_positive_power_bound {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν p : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ), 0 < r →
      ∀ v : ℝ × (Fin N → ℝ) → ℝ,
      (∀ t ∈ Ioo (t₀ - r ^ 2) t₀, ∀ x, 0 ≤ v (t, x)) →
      IsLocalWeakSolution G hq hqpos hw hspan
        (fun _ _ i j => if i = j then 1 else 0)
        ⟨Ioo (t₀ - r ^ 2) t₀, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x₀ r,
          isOpen_horizontalBall G hq hqpos hspan x₀ r⟩ (fun t x => v (t, x)) →
      eLpNormEssSup v (volume.restrict
        (Ioo (t₀ - r ^ 2 / 2) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ (r / 2))) ≤
        ENNReal.ofReal C * (ENNReal.ofReal ((r ^ (G.homogeneousDimension + 2))⁻¹) ^ (1 / p) *
          eLpNorm v (ENNReal.ofReal p) (volume.restrict
            (Ioo (t₀ - r ^ 2) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ r))) := by
  obtain ⟨C, hC, hmean⟩ := exists_uniform_matrix_cylinder_positive_power_bound
    G hq hqpos hspan hw hν hp 1 1 (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro t₀ x₀ r hr v hv0 hweak
  exact hmean t₀ x₀ r hr v (fun _ _ i j => if i = j then 1 else 0)
    (nonneg_ae_on_product_of_nonneg_on isOpen_Ioo.measurableSet
      (isOpen_horizontalBall G hq hqpos hspan x₀ r).measurableSet
      (fun t ht x _ => hv0 t ht x)) hweak (fun _ _ => measurable_const)
    (identity_coefficients_ellipticity N q)

end HeatKernel

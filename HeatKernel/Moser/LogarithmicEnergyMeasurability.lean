-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionEnergyInterface
public import HeatKernel.Bridge.ParabolicGradientMeasurability
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Time measurability of the logarithmic cutoff energy -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- The gradient of the common solution interface gives a measurable logarithmic
energy curve for every measurable spatial weight vanishing outside the domain.
No change of gradient or spatial energy integrability assumption is needed. -/
theorem WeakSolutionEnergyInterface.aestronglyMeasurable_logarithmic_energy
    {N q : ℕ} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (h : WeakSolutionEnergyInterface X a I U u g)
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j))
    (hu : Measurable (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2))
    {w : (Fin N → ℝ) → ℝ} (hw : Measurable w)
    (hwzero : ∀ y ∉ (U : Set (Fin N → ℝ)), w y = 0) (c : ℝ) :
    AEStronglyMeasurable (fun s => (∫ y, w y^2)⁻¹ *
      ∫ y, ∑ i, ∑ j, a s y i j *
        (w y * ((u s y + c)⁻¹ * g j s y)) *
        (w y * ((u s y + c)⁻¹ * g i s y)))
      (volume.restrict (I : Set ℝ)) := by
  let μ := volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))
  let d := fun i (z : ℝ × (Fin N → ℝ)) =>
    w z.2 * ((u z.1 z.2 + c)⁻¹ * g i z.1 z.2)
  have hd (i : Fin q) : AEStronglyMeasurable (d i) μ := by
    exact (hw.comp measurable_snd).aestronglyMeasurable.fun_mul
      ((hu.aestronglyMeasurable.fun_add aestronglyMeasurable_const).fun_inv₀.fun_mul
        (h.local_bounds.aestronglyMeasurable_gradient i))
  have he : AEStronglyMeasurable (fun z : ℝ × (Fin N → ℝ) =>
      ∑ i, ∑ j, a z.1 z.2 i j * d j z * d i z) μ := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro i _
    apply Finset.aestronglyMeasurable_fun_sum
    intro j _
    exact ((ha i j).aestronglyMeasurable.fun_mul (hd j)).fun_mul (hd i)
  have hep : AEStronglyMeasurable (fun z : ℝ × (Fin N → ℝ) =>
      ∑ i, ∑ j, a z.1 z.2 i j * d j z * d i z)
      ((volume.restrict (I : Set ℝ)).prod
        (volume.restrict (U : Set (Fin N → ℝ)))) := by
    simpa only [μ, Measure.prod_restrict, ← Measure.volume_eq_prod] using he
  have hi := hep.integral_prod_right'
  have heq (s : ℝ) : (∫ y in (U : Set (Fin N → ℝ)),
      ∑ i, ∑ j, a s y i j * d j (s, y) * d i (s, y)) =
      ∫ y, ∑ i, ∑ j, a s y i j * d j (s, y) * d i (s, y) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    simp only [d, hwzero y hy, zero_mul, mul_zero, Finset.sum_const_zero]
  simpa only [heq, d] using hi.const_mul (∫ y, w y^2)⁻¹

/-- Positive semidefinite coefficients make the literal normalized logarithmic
cutoff energy nonnegative at almost every time, using the original gradient. -/
theorem ae_nonneg_logarithmic_matrix_energy {N q : ℕ}
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    (hpos : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume, ∀ ξ : Fin q → ℝ,
      0 ≤ ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j)
    (u : ℝ → (Fin N → ℝ) → ℝ) (g : Fin q → ℝ → (Fin N → ℝ) → ℝ)
    (w : (Fin N → ℝ) → ℝ) (c : ℝ) :
    ∀ᵐ s ∂volume, 0 ≤ (∫ y, w y^2)⁻¹ *
      ∫ y, ∑ i, ∑ j, a s y i j *
        (w y * ((u s y + c)⁻¹ * g j s y)) *
        (w y * ((u s y + c)⁻¹ * g i s y)) := by
  have hp : ∀ᵐ s ∂volume, ∀ᵐ y ∂volume, ∀ ξ : Fin q → ℝ,
      0 ≤ ∑ i, ∑ j, a s y i j * ξ i * ξ j := by
    exact Measure.ae_ae_of_ae_prod (by
      simpa only [Measure.volume_eq_prod] using hpos)
  filter_upwards [hp] with s hs
  apply mul_nonneg
  · exact inv_nonneg.mpr (integral_nonneg fun y => sq_nonneg (w y))
  · apply integral_nonneg_of_ae
    filter_upwards [hs] with y hy
    change (0 : ℝ) ≤ ∑ i, ∑ j, a s y i j *
      (w y * ((u s y + c)⁻¹ * g j s y)) *
      (w y * ((u s y + c)⁻¹ * g i s y))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      hy (fun i => w y * ((u s y + c)⁻¹ * g i s y))

end HeatKernel

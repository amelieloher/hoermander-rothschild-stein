-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.WeightedEnergyIdentity
public import HeatKernel.Form.EnergyDensity
import Mathlib.Tactic

/-! # Weighted identities for the concrete horizontal form

The concrete form density becomes the weighted horizontal integrand when an
exponential product has the Leibniz gradient. A form equation then identifies
the weighted trajectory inner product with minus this integral.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped BigOperators
namespace HeatKernel.Gaussian

/-- Two equal exponential weights in a real L² pairing combine into one
weight with twice the parameter. -/
theorem inner_exponential_eq_inner_double_exponential {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ψ : X → ℝ) (hψ : AEStronglyMeasurable ψ μ)
    (B : ℝ) (hB : ∀ x, |ψ x| ≤ B) (a : ℝ) (u v : Lp ℝ 2 μ) :
    inner ℝ (exponentialMultiplication μ ψ hψ B hB a u)
      (exponentialMultiplication μ ψ hψ B hB a v) =
        inner ℝ v (exponentialMultiplication μ ψ hψ B hB (2 * a) u) := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_exponentialMultiplication μ ψ hψ B hB a u,
    coeFn_exponentialMultiplication μ ψ hψ B hB a v,
    coeFn_exponentialMultiplication μ ψ hψ B hB (2 * a) u] with x hu hv hw
  rw [hu, hv, hw]
  simp only [RCLike.inner_apply, conj_trivial]
  have he : Real.exp (2 * a * ψ x) = Real.exp (a * ψ x) * Real.exp (a * ψ x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

/-- The Leibniz gradient of an exponential product identifies its concrete
horizontal form density with the weighted energy integrand. -/
theorem horizontalEnergy_eq_weighted_integral_of_gradient {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (u w : energyGraph U X) (ψ : (Fin N → ℝ) → ℝ) (a : ℝ)
    (h : (Fin N → ℝ) → Fin q → ℝ)
    (hw : ∀ i, (w : GradientSpace U q).snd i =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
      fun x ↦ Real.exp (2 * a * ψ x) *
        ((u : GradientSpace U q).snd i x + 2 * a * energyInclusion U X u x * h x i)) :
    horizontalEnergy U X u w =
      ∫ x, Real.exp (2 * a * ψ x) * ∑ i, (u : GradientSpace U q).snd i x *
        ((u : GradientSpace U q).snd i x + 2 * a * energyInclusion U X u x * h x i)
        ∂volume.restrict (U : Set (Fin N → ℝ)) := by
  rw [horizontalEnergy_eq_integral_density]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr hw] with x hx
  simp only [horizontalEnergyDensity, hx, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A form equation and exponential product inclusion identify the weighted
trajectory inner product with minus the horizontal form. -/
theorem inner_exponential_eq_neg_horizontalEnergy_of_form_equation {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (u w : energyGraph U X) (v : SpatialL2 U)
    (ψ : (Fin N → ℝ) → ℝ)
    (hψ : AEStronglyMeasurable ψ (volume.restrict (U : Set (Fin N → ℝ))))
    (B : ℝ) (hB : ∀ x, |ψ x| ≤ B) (a : ℝ)
    (hw : energyInclusion U X w =
      exponentialMultiplication (volume.restrict (U : Set (Fin N → ℝ))) ψ hψ B hB
        (2 * a) (energyInclusion U X u))
    (hform : horizontalEnergy U X u w = inner ℝ (-v) (energyInclusion U X w)) :
    inner ℝ (exponentialMultiplication (volume.restrict (U : Set (Fin N → ℝ))) ψ hψ B hB a
      (energyInclusion U X u))
      (exponentialMultiplication (volume.restrict (U : Set (Fin N → ℝ))) ψ hψ B hB a v) =
        -horizontalEnergy U X u w := by
  rw [inner_exponential_eq_inner_double_exponential, ← hw]
  rw [inner_neg_left] at hform
  linarith

/-- The exponential Leibniz gradient makes the weighted horizontal form
integrable, because it is the density of a pair of form-domain functions. -/
theorem integrable_weighted_horizontal_form_of_gradient {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (u w : energyGraph U X) (ψ : (Fin N → ℝ) → ℝ) (a : ℝ)
    (h : (Fin N → ℝ) → Fin q → ℝ)
    (hw : ∀ i, (w : GradientSpace U q).snd i =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
      fun x ↦ Real.exp (2 * a * ψ x) *
        ((u : GradientSpace U q).snd i x + 2 * a * energyInclusion U X u x * h x i)) :
    Integrable (fun x ↦ Real.exp (2 * a * ψ x) * ∑ i, (u : GradientSpace U q).snd i x *
      ((u : GradientSpace U q).snd i x + 2 * a * energyInclusion U X u x * h x i))
      (volume.restrict (U : Set (Fin N → ℝ))) := by
  apply (integrable_horizontalEnergyDensity U X u w).congr
  filter_upwards [ae_all_iff.mpr hw] with x hx
  simp only [horizontalEnergyDensity, hx, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- An exponential product in the concrete form domain, its Leibniz gradient,
and the generator form equation imply the weighted energy inequality. -/
theorem inner_exponential_le_of_horizontal_form_equation {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (u w : energyGraph U X) (v : SpatialL2 U)
    (ψ : (Fin N → ℝ) → ℝ)
    (hψ : AEStronglyMeasurable ψ (volume.restrict (U : Set (Fin N → ℝ))))
    (B : ℝ) (hB : ∀ x, |ψ x| ≤ B) (a : ℝ)
    (h : (Fin N → ℝ) → Fin q → ℝ)
    (hh : ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), ∑ i, h x i ^ 2 ≤ 1)
    (hwf : energyInclusion U X w =
      exponentialMultiplication (volume.restrict (U : Set (Fin N → ℝ))) ψ hψ B hB
        (2 * a) (energyInclusion U X u))
    (hwg : ∀ i, (w : GradientSpace U q).snd i =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
      fun x ↦ Real.exp (2 * a * ψ x) *
        ((u : GradientSpace U q).snd i x + 2 * a * energyInclusion U X u x * h x i))
    (hform : horizontalEnergy U X u w = inner ℝ (-v) (energyInclusion U X w)) :
    inner ℝ (exponentialMultiplication (volume.restrict (U : Set (Fin N → ℝ))) ψ hψ B hB a
      (energyInclusion U X u))
      (exponentialMultiplication (volume.restrict (U : Set (Fin N → ℝ))) ψ hψ B hB a v) ≤
        a ^ 2 * ‖exponentialMultiplication (volume.restrict (U : Set (Fin N → ℝ))) ψ hψ B hB a
          (energyInclusion U X u)‖ ^ 2 := by
  apply inner_exponential_le_of_horizontal_form_identity _ ψ hψ B hB a
    (energyInclusion U X u) v (fun x i ↦ (u : GradientSpace U q).snd i x) h hh
    (integrable_weighted_horizontal_form_of_gradient U X u w ψ a h hwg)
  rw [inner_exponential_eq_neg_horizontalEnergy_of_form_equation U X u w v ψ hψ B hB a hwf hform,
    horizontalEnergy_eq_weighted_integral_of_gradient U X u w ψ a h hwg]

end HeatKernel.Gaussian

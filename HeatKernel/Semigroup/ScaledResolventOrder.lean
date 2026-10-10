-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.ScaledFormResolvent
public import HeatKernel.Form.TruncationEnergy
public import HeatKernel.Semigroup.TruncationPairings

/-! # Order bounds for the scaled resolvent

Testing the variational equation with the negative part or a positive-level truncation
forces the corresponding part to vanish.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set TopologicalSpace
namespace HeatKernel
variable {N q : ℕ} (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))

include hX in
theorem scaledHorizontalFormResolvent_nonneg (scale : ℝ) (hscale : 0 < scale)
    (f : SpatialL2 (N := N) ⊤) (hf : ∀ᵐ x ∂volume, 0 ≤ f x) :
    ∀ᵐ x ∂volume, 0 ≤ scaledHorizontalFormResolvent ⊤ X scale hscale f x := by
  rw [scaledHorizontalFormResolvent_apply]
  let u := scaledEnergySolution ⊤ X scale hscale f
  obtain ⟨z, hz, he⟩ := exists_energyGraph_negativePart_energy_eq X hX u
  have hz' : energyInclusion ⊤ X z =ᵐ[volume]
      fun x => max (-(energyInclusion ⊤ X u) x) 0 := hz
  have hp : inner ℝ (energyInclusion ⊤ X u) (energyInclusion ⊤ X z) =
      -‖energyInclusion ⊤ X z‖ ^ 2 := by
    apply inner_negativePart_eq
    simpa only [Opens.coe_top, Measure.restrict_univ] using hz'
  have hr : 0 ≤ inner ℝ f (energyInclusion ⊤ X z) := by
    rw [L2.inner_def]
    apply integral_nonneg_of_ae
    change ∀ᵐ x ∂volume.restrict (⊤ : Opens (Fin N → ℝ)),
      0 ≤ inner ℝ (f x) ((energyInclusion ⊤ X z) x)
    have H : ∀ᵐ x ∂volume, 0 ≤ inner ℝ (f x) ((energyInclusion ⊤ X z) x) := by
      filter_upwards [hf, hz'] with x hfx hzx
      rw [Real.inner_apply, hzx]
      exact mul_nonneg hfx (le_max_right _ _)
    simpa only [Opens.coe_top, Measure.restrict_univ] using H
  have hv := scaledEnergySolution_equation ⊤ X scale hscale f z
  change inner ℝ (energyInclusion ⊤ X u) (energyInclusion ⊤ X z) +
    scale * horizontalEnergy ⊤ X u z = inner ℝ f (energyInclusion ⊤ X z) at hv
  rw [hp, he] at hv
  have henergy := horizontalEnergy_self_nonneg ⊤ X z
  have hzero : energyInclusion ⊤ X z = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (energyInclusion ⊤ X z), mul_nonneg hscale.le henergy]
  have hzae : energyInclusion ⊤ X z =ᵐ[volume] (0 : (Fin N → ℝ) → ℝ) := by
    rw [hzero]
    have H := Lp.coeFn_zero ℝ 2 (volume.restrict (Set.univ : Set (Fin N → ℝ)))
    simpa only [Opens.coe_top, Measure.restrict_univ] using H
  filter_upwards [hz', hzae] with x hx hz0
  simp only [Pi.zero_apply] at hz0
  change 0 ≤ (energyInclusion ⊤ X u) x
  have hneg := le_max_left (-(energyInclusion ⊤ X u) x) 0
  rw [← hx, hz0] at hneg
  linarith

include hX in
theorem scaledHorizontalFormResolvent_le_one (scale : ℝ) (hscale : 0 < scale)
    (f : SpatialL2 (N := N) ⊤) (hf : ∀ᵐ x ∂volume, f x ≤ 1) :
    ∀ᵐ x ∂volume, scaledHorizontalFormResolvent ⊤ X scale hscale f x ≤ 1 := by
  rw [scaledHorizontalFormResolvent_apply]
  let u := scaledEnergySolution ⊤ X scale hscale f
  obtain ⟨z, hz, he⟩ := exists_energyGraph_positiveLevel_energy_eq X hX u 1 zero_le_one
  have hz' : energyInclusion ⊤ X z =ᵐ[volume]
      fun x => max ((energyInclusion ⊤ X u) x - 1) 0 := hz
  have hp : ‖energyInclusion ⊤ X z‖ ^ 2 ≤
      inner ℝ (energyInclusion ⊤ X u) (energyInclusion ⊤ X z) -
        inner ℝ f (energyInclusion ⊤ X z) := by
    apply norm_sq_positiveLevel_le_pairing
    · simpa only [Opens.coe_top, Measure.restrict_univ] using hf
    · simpa only [Opens.coe_top, Measure.restrict_univ] using hz'
  have hv := scaledEnergySolution_equation ⊤ X scale hscale f z
  change inner ℝ (energyInclusion ⊤ X u) (energyInclusion ⊤ X z) +
    scale * horizontalEnergy ⊤ X u z = inner ℝ f (energyInclusion ⊤ X z) at hv
  rw [he] at hv
  have henergy := horizontalEnergy_self_nonneg ⊤ X z
  have hzero : energyInclusion ⊤ X z = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (energyInclusion ⊤ X z), mul_nonneg hscale.le henergy]
  have hzae : energyInclusion ⊤ X z =ᵐ[volume] (0 : (Fin N → ℝ) → ℝ) := by
    rw [hzero]
    have H := Lp.coeFn_zero ℝ 2 (volume.restrict (Set.univ : Set (Fin N → ℝ)))
    simpa only [Opens.coe_top, Measure.restrict_univ] using H
  filter_upwards [hz', hzae] with x hx hz0
  simp only [Pi.zero_apply] at hz0
  change (energyInclusion ⊤ X u) x ≤ 1
  have hpos := le_max_left ((energyInclusion ⊤ X u) x - 1) 0
  rw [← hx, hz0] at hpos
  linarith

end HeatKernel

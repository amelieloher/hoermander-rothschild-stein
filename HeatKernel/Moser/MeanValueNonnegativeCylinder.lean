-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionEnergyInterface
public import HeatKernel.Moser.WeakSolutionCutoffDualEquation
public import HeatKernel.Moser.WeakSolutionEnergyIdentityLimits
import Mathlib.Tactic

/-! # Almost everywhere nonnegativity on product cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- Pointwise nonnegativity on a measurable cylinder gives its almost everywhere form. -/
theorem nonneg_ae_on_product_of_nonneg_on {N : ℕ}
    {I : Set ℝ} {U : Set (Fin N → ℝ)} (hI : MeasurableSet I) (hU : MeasurableSet U)
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : ∀ t ∈ I, ∀ x ∈ U, 0 ≤ u t x) :
    ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume.restrict (I ×ˢ U), 0 ≤ u z.1 z.2 := by
  filter_upwards [self_mem_ae_restrict (hI.prod hU)] with z hz
  exact hu z.1 hz.1 z.2 hz.2

/-- Nonnegativity on a measurable product cylinder holds on almost every spatial slice. -/
theorem ae_ae_nonneg_of_nonneg_on_product {N : ℕ}
    {I : Set ℝ} {U : Set (Fin N → ℝ)} (hI : MeasurableSet I) (hU : MeasurableSet U)
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume.restrict (I ×ˢ U), 0 ≤ u z.1 z.2) :
    ∀ᵐ t ∂volume, ∀ᵐ x ∂volume, t ∈ I → x ∈ U → 0 ≤ u t x := by
  have h := Measure.ae_ae_of_ae_prod ((ae_restrict_iff' (hI.prod hU)).mp hu)
  filter_upwards [h] with t ht
  exact ht.mono fun x hx htI hxU => hx ⟨htI, hxU⟩

end HeatKernel

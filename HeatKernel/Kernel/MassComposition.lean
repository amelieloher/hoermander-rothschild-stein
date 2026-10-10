-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Prod

/-! # Multiplication of common kernel masses

Integrable nonnegative rows and a common row mass give absolute integrability of
the composition integrand. Fubini then turns kernel composition into multiplication
of the two row masses.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- Composition multiplies the common masses of nonnegative integrable kernel rows. -/
theorem mass_composition_of_integrable_nonnegative_kernels {X : Type*}
    [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (k l r : X → X → ℝ) (m n a : ℝ)
    (hk : ∀ x y, 0 ≤ k x y) (hl : ∀ x y, 0 ≤ l x y)
    (hik : ∀ x, Integrable (k x) μ) (hil : ∀ x, Integrable (l x) μ)
    (hml : AEStronglyMeasurable (fun p : X × X => l p.1 p.2) (μ.prod μ))
    (hmk : ∀ x, ∫ y, k x y ∂μ = m) (hmlmass : ∀ x, ∫ y, l x y ∂μ = n)
    (hmr : ∀ x, ∫ y, r x y ∂μ = a)
    (hcomp : ∀ x y, ∫ z, k x z * l z y ∂μ = r x y) (x : X) : a = m * n := by
  have hsm : AEStronglyMeasurable (fun p : X × X => k x p.1 * l p.1 p.2) (μ.prod μ) :=
    ((hik x).aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))).mul hml
  have hi : Integrable (fun p : X × X => k x p.1 * l p.1 p.2) (μ.prod μ) := by
    apply (integrable_prod_iff hsm).mpr
    constructor
    · exact Filter.Eventually.of_forall fun z => (hil z).const_mul (k x z)
    · change Integrable (fun z => ∫ y, ‖k x z * l z y‖ ∂μ) μ
      have hknorm (z : X) : ‖k x z‖ = k x z := Real.norm_of_nonneg (hk x z)
      have hlnorm (z y : X) : ‖l z y‖ = l z y := Real.norm_of_nonneg (hl z y)
      simpa only [norm_mul, hknorm, hlnorm, integral_const_mul, hmlmass] using
        (hik x).mul_const n
  calc
    a = ∫ y, r x y ∂μ := (hmr x).symm
    _ = ∫ y, ∫ z, k x z * l z y ∂μ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => (hcomp x y).symm
    _ = ∫ z, ∫ y, k x z * l z y ∂μ ∂μ := (integral_integral_swap hi).symm
    _ = ∫ z, k x z * n ∂μ := by simp only [integral_const_mul, hmlmass]
    _ = m * n := by rw [integral_mul_const, hmk]

end HeatKernel

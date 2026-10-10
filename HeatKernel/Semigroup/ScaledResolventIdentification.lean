-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.ScaledResolventEquation
public import HeatKernel.Semigroup.ResolventDenominator
public import HeatKernel.Semigroup.ComplexL2Positivity
public import HeatKernel.Semigroup.PositiveResolventSpectrum

/-! # Identification of the variational and spectral resolvents -/

@[expose] public section
noncomputable section
open MeasureTheory Set TopologicalSpace
namespace HeatKernel
variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

theorem l2OfReal_scaledHorizontalFormResolvent
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    (scale : ℝ) (hscale : 0 < scale) (f : SpatialL2 U) :
    l2OfReal (volume.restrict (U : Set (Fin N → ℝ)))
      (scaledHorizontalFormResolvent U X scale hscale f) =
    scaledResolventCfcOperator
      (complexL2Extension (volume.restrict (U : Set (Fin N → ℝ))) (horizontalFormResolvent U X))
      scale (l2OfReal (volume.restrict (U : Set (Fin N → ℝ))) f) := by
  let μ := volume.restrict (U : Set (Fin N → ℝ))
  let R := horizontalFormResolvent U X
  let C := complexL2Extension μ R
  have hpos : C.IsPositive := complexL2Extension_isPositive μ R (horizontalFormResolvent_isPositive U X)
  have hspec : spectrum ℝ C ⊆ Icc (0 : ℝ) 1 :=
    spectrum_subset_Icc_of_isPositive_norm_le_one C hpos
      (norm_complexL2Extension_le_one μ R (norm_horizontalFormResolvent_le_one U X))
  apply resolvent_denominator_injective C hpos.isSelfAdjoint hspec scale hscale
  have hform := congrArg (l2OfReal μ)
    (scaledHorizontalFormResolvent_equation U X hX scale hscale f)
  have hcfc := congrArg (fun T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ => T (l2OfReal μ f))
    (scaledResolventCfcOperator_equation C hpos.isSelfAdjoint hspec scale hscale)
  change (C + scale • (1 - C))
    (l2OfReal μ (scaledHorizontalFormResolvent U X scale hscale f)) =
    (C + scale • (1 - C)) (scaledResolventCfcOperator C scale (l2OfReal μ f))
  rw [mul_apply_eq_comp] at hcfc
  calc
    _ = C (l2OfReal μ f) := by
      simpa only [C, R, add_apply, smul_apply, sub_apply, one_apply_eq_self,
        complexL2Extension_ofReal, map_add, map_smul, map_sub] using hform
    _ = _ := hcfc.symm

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.ScaledResolventIdentification
public import HeatKernel.Semigroup.HorizontalHeatOperators
public import HeatKernel.Semigroup.PositiveTimeHeatOperators

/-! # Euler approximation by the horizontal form resolvent -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace HeatKernel
variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

theorem l2OfReal_scaledHorizontalFormResolvent_pow
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    (scale : ℝ) (hscale : 0 < scale) (n : ℕ) (f : SpatialL2 U) :
    l2OfReal (volume.restrict (U : Set (Fin N → ℝ)))
      ((scaledHorizontalFormResolvent U X scale hscale ^ n) f) =
    (scaledResolventCfcOperator
      (complexL2Extension (volume.restrict (U : Set (Fin N → ℝ))) (horizontalFormResolvent U X))
      scale ^ n) (l2OfReal (volume.restrict (U : Set (Fin N → ℝ))) f) := by
  induction n with
  | zero => simp only [pow_zero, one_apply_eq_self]
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, l2OfReal_scaledHorizontalFormResolvent U X hX scale hscale,
      ih, pow_succ', mul_apply_eq_comp]

/-- Implicit Euler approximants with a positive number of time steps. -/
def horizontalEulerOperator (t : ℝ) (ht : 0 < t) (n : ℕ) : SpatialL2 U →L[ℝ] SpatialL2 U :=
  scaledHorizontalFormResolvent U X (t / (n + 1 : ℕ))
    (div_pos ht (by exact_mod_cast Nat.succ_pos n)) ^ (n + 1)

theorem tendsto_horizontalEulerOperator_apply
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    (t : ℝ) (ht : 0 < t) (f : SpatialL2 U) :
    Tendsto (fun n => horizontalEulerOperator U X t ht n f) atTop
      (𝓝 (horizontalHeatOperator U X t.toNNReal f)) := by
  let μ := volume.restrict (U : Set (Fin N → ℝ))
  let R := horizontalFormResolvent U X
  let C := complexL2Extension μ R
  have hpos : C.IsPositive := complexL2Extension_isPositive μ R (horizontalFormResolvent_isPositive U X)
  have hspec : spectrum ℝ C ⊆ Icc (0 : ℝ) 1 :=
    spectrum_subset_Icc_of_isPositive_norm_le_one C hpos
      (norm_complexL2Extension_le_one μ R (norm_horizontalFormResolvent_le_one U X))
  have hc := (tendsto_scaledResolventCfcOperator_pow C hpos.isSelfAdjoint hspec ht).comp
    (tendsto_add_atTop_nat 1)
  have hev : Continuous (fun T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ => T (l2OfReal μ f)) :=
    continuous_id.clm_apply continuous_const
  have he := (l2RealPart μ).continuous.tendsto _ |>.comp ((hev.tendsto _).comp hc)
  have htime := heatOperator_toNNReal_of_pos C ht
  have hlim : l2RealPart μ (positiveTimeHeatOperator C t (l2OfReal μ f)) =
      horizontalHeatOperator U X t.toNNReal f := by
    rw [← htime, ← l2OfReal_realL2HeatOperator μ R (horizontalFormResolvent_isPositive U X)
      (norm_horizontalFormResolvent_le_one U X), l2RealPart_ofReal]
    rfl
  rw [hlim] at he
  apply he.congr'
  exact Filter.Eventually.of_forall (fun n => by
    have hp := l2OfReal_scaledHorizontalFormResolvent_pow U X hX (t / (n + 1 : ℕ))
      (div_pos ht (by exact_mod_cast Nat.succ_pos n)) (n + 1) f
    simpa only [horizontalEulerOperator, Function.comp_apply] using
      (congrArg (l2RealPart μ) hp).symm.trans (l2RealPart_ofReal μ _))

end HeatKernel

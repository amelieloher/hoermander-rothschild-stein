-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.NonnegativeTimeMultipliers
public import HeatKernel.Semigroup.RealFunctionalCalculus

/-! # Heat operators from a bounded self-adjoint resolvent

The spectral interval and invariant real subspace are explicit inputs. The construction
therefore applies independently of any particular closed quadratic form.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal

namespace HeatKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The heat operator obtained by real continuous functional calculus. -/
def heatOperator (R : E →L[ℂ] E) (t : ℝ≥0) : E →L[ℂ] E :=
  cfc (semigroupMultiplier t) R

theorem heatOperator_zero (R : E →L[ℂ] E) (hR : IsSelfAdjoint R) :
    heatOperator R 0 = 1 := by
  unfold heatOperator
  simpa only [semigroupMultiplier_zero] using cfc_const_one ℝ R hR

theorem heatOperator_add (R : E →L[ℂ] E) (s t : ℝ≥0) :
    heatOperator R (s + t) = heatOperator R s * heatOperator R t := by
  unfold heatOperator
  rw [show semigroupMultiplier (s + t) =
    (fun r => semigroupMultiplier s r * semigroupMultiplier t r) from
    funext (semigroupMultiplier_add s t)]
  exact cfc_mul _ _ R (continuous_semigroupMultiplier s).continuousOn
    (continuous_semigroupMultiplier t).continuousOn

theorem norm_heatOperator_le (R : E →L[ℂ] E)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (t : ℝ≥0) : ‖heatOperator R t‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro r hr
  have h := semigroupMultiplier_mem_Icc t (hspec hr)
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

theorem heatOperator_isSelfAdjoint (R : E →L[ℂ] E) (t : ℝ≥0) :
    IsSelfAdjoint (heatOperator R t) := cfc_predicate _ R

theorem mapsTo_heatOperator_of_mapsTo (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (R : E →L[ℂ] E) (hR : IsSelfAdjoint R) (hinv : MapsTo R S S)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (t : ℝ≥0) :
    MapsTo (heatOperator R t) S S :=
  mapsTo_cfc_of_mapsTo S hS R hR hinv hspec _
    (continuous_semigroupMultiplier t).continuousOn

theorem norm_heatOperator_sub_mul_le (R : E →L[ℂ] E) (hR : IsSelfAdjoint R)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (s t : ℝ≥0) :
    ‖(heatOperator R t - heatOperator R s) * R‖ ≤ dist t s := by
  unfold heatOperator
  rw [← cfc_sub _ _ R (continuous_semigroupMultiplier t).continuousOn
    (continuous_semigroupMultiplier s).continuousOn]
  conv_lhs => arg 1; arg 2; rw [← cfc_id' ℝ R hR]
  rw [← cfc_mul (fun r => semigroupMultiplier t r - semigroupMultiplier s r)
    (fun r : ℝ => r) R
    ((continuous_semigroupMultiplier t).sub (continuous_semigroupMultiplier s)).continuousOn
    continuous_id.continuousOn]
  apply norm_cfc_le dist_nonneg
  intro r hr
  have hr' := hspec hr
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hr'.1, mul_comm]
    using weighted_semigroupMultiplier_sub_le s t hr'

end HeatKernel

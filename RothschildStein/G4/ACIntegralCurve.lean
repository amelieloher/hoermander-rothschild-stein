-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ConstantControl
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace RothschildStein.G4

/-- An absolutely continuous finite-dimensional curve satisfies
its coordinate integral equation for its actual a.e. ODE right-hand side.
This bridges BB's AC control definition to classical integral curves. -/
theorem ac_curve_coordinate_integral {n : ℕ} {γ β : ℝ → (Fin n → ℝ)}
    (hac : AbsolutelyContinuousOnInterval γ 0 1)
    (hd : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), HasDerivAt γ (β t) t)
    {t : ℝ} (ht : t ∈ Icc 0 1) (i : Fin n) :
    γ t i = γ 0 i + ∫ u in (0 : ℝ)..t, β u i := by
  have hscalar := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).lipschitzWith
    |>.comp_absolutelyContinuousOnInterval hac
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le ht.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl ht.2
  have hint := (hscalar.mono hsub).integral_deriv_eq_sub
  have he : (∫ u in (0 : ℝ)..t, deriv (fun v => γ v i) u) =
      ∫ u in (0 : ℝ)..t, β u i := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_imp_of_ae_restrict hd] with u hu humem
    have hu01 : u ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le ht.1] at humem
      exact ⟨humem.1.le, humem.2.trans ht.2⟩
    exact (hasDerivAt_pi.mp (hu hu01) i).deriv
  change (∫ u in (0 : ℝ)..t, deriv (fun v => γ v i) u) = γ t i - γ 0 i at hint
  rw [he] at hint
  linarith

end RothschildStein.G4

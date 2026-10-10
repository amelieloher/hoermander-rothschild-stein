-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.GraphForm

/-! # The global spatial form space and full-volume L²

Equality of measures gives a real L² isometry which preserves scalar
representatives. In particular, restriction to the whole open set is harmless.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace

namespace HeatKernel

/-- Equal measures give a canonical isometry of real L² spaces. -/
def realL2MeasureEquiv {α : Type*} [MeasurableSpace α] {μ ν : Measure α} (h : μ = ν) :
    Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 ν := by
  subst ν
  exact LinearIsometryEquiv.refl ℝ (Lp ℝ 2 μ)

/-- Transport between equal measures preserves scalar representatives almost everywhere. -/
theorem ae_realL2MeasureEquiv {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    (h : μ = ν) (f : Lp ℝ 2 μ) : realL2MeasureEquiv h f =ᵐ[ν] f := by
  subst ν
  exact Filter.EventuallyEq.rfl

/-- The spatial form space over the whole open set is isometric to full-volume L². -/
def globalSpatialL2Equiv (N : ℕ) :
    SpatialL2 (N := N) ⊤ ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure (Fin N → ℝ)) :=
  realL2MeasureEquiv (by simp only [Opens.coe_top, Measure.restrict_univ])

/-- The global spatial isometry preserves the represented scalar function. -/
theorem ae_globalSpatialL2Equiv {N : ℕ} (f : SpatialL2 (N := N) ⊤) :
    globalSpatialL2Equiv N f =ᵐ[volume] f := ae_realL2MeasureEquiv _ f

/-- The inverse global spatial isometry also preserves scalar representatives. -/
theorem ae_globalSpatialL2Equiv_symm {N : ℕ}
    (f : Lp ℝ 2 (volume : Measure (Fin N → ℝ))) :
    (globalSpatialL2Equiv N).symm f =ᵐ[volume] f := by
  have h := ae_globalSpatialL2Equiv ((globalSpatialL2Equiv N).symm f)
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h.symm

end HeatKernel

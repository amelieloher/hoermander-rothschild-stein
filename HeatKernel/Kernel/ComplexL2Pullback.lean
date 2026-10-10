-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-! # Complex unitary L² pullback by measure-preserving equivalences

Pullback by a measure-preserving measurable equivalence has inverse pullback by
the inverse equivalence, and therefore defines a complex Hilbert-space isometry.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- Pullback by a measure-preserving measurable equivalence is a unitary map on complex L². -/
def complexMeasurePreservingL2Equiv {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ := by
  let hi := MeasurePreserving.symm e he
  refine { Lp.compMeasurePreservingₗᵢ ℂ e he with
    invFun := Lp.compMeasurePreserving e.symm hi
    left_inv := ?_
    right_inv := ?_ }
  · intro f
    change Lp.compMeasurePreserving e.symm hi (Lp.compMeasurePreserving e he f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f he hi]
    have hfun : (e : X → X) ∘ e.symm = id := funext e.apply_symm_apply
    simp only [hfun, Lp.compMeasurePreserving_id_apply]
  · intro f
    change Lp.compMeasurePreserving e he (Lp.compMeasurePreserving e.symm hi f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f hi he]
    have hfun : (e.symm : X → X) ∘ e = id := funext e.symm_apply_apply
    simp only [hfun, Lp.compMeasurePreserving_id_apply]

/-- The unitary pullback has its expected almost-everywhere representative. -/
theorem ae_complexMeasurePreservingL2Equiv_apply {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (f : Lp ℂ 2 μ) :
    complexMeasurePreservingL2Equiv μ e he f =ᵐ[μ] fun x => f (e x) :=
  Lp.coeFn_compMeasurePreserving f he

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.EnergyCurveFlux
public import HeatKernel.Form.FluxPairing
import Mathlib.Tactic.Linter

/-! # Integrable coefficient form values along energy curves -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal

namespace HeatKernel

/-- The scalar product of two Bochner L² curves is integrable. -/
theorem integrable_inner_of_memLp_two {T E : Type*} [MeasurableSpace T]
    {μ : Measure T} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : T → E} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun t => inner ℝ (u t) (v t)) μ := by
  have H := L2.integrable_inner (𝕜 := ℝ) (hu.toLp u) (hv.toLp v)
  apply H.congr
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with t ht hs
  rw [ht, hs]

/-- Bounded jointly measurable coefficients give integrable form values when both energy
arguments vary as Bochner L² curves. -/
theorem integrable_coefficientEnergy_curves {T : Type*} [MeasurableSpace T]
    {μ : Measure T} {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (a : Fin q → Fin q → T × (Fin N → ℝ) → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i j, AEStronglyMeasurable (a i j)
      (μ.prod (volume.restrict (U : Set (Fin N → ℝ)))))
    (hb : ∀ i j, ∀ᵐ z ∂μ.prod (volume.restrict (U : Set (Fin N → ℝ))), ‖a i j z‖ ≤ C)
    (v w : T → energyGraph U X) (hv : MemLp v 2 μ) (hw : MemLp w 2 μ) :
    Integrable (fun t => coefficientEnergy U X (fun i j x => a i j (t, x)) (v t) (w t)) μ := by
  obtain ⟨J, hJ, hr⟩ := exists_Bochner_energy_flux_of_curve U X a hC ha hb v hv
  have H := integrable_inner_of_memLp_two hJ ((energyGradient U X).comp_memLp' hw)
  apply H.congr
  filter_upwards [ae_all_iff.mpr hr] with t ht
  exact (coefficientEnergy_eq_inner_flux U X (fun i j x => a i j (t, x))
    (v t) (w t) (J t) ht).symm



end HeatKernel

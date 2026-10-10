-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.BochnerCurveFlux
public import HeatKernel.Form.GraphForm
import Mathlib.Tactic.Linter

/-! # Time-dependent fluxes of horizontal energy curves -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal

namespace HeatKernel

/-- Every Bochner square integrable energy curve has a square integrable coefficient flux.
Joint measurability and boundedness of the coefficients suffice; joint representatives of the
energy curve are not additional hypotheses. -/
theorem exists_Bochner_energy_flux_of_curve {T : Type*} [MeasurableSpace T]
    {μ : Measure T} {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (a : Fin q → Fin q → T × (Fin N → ℝ) → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i j, AEStronglyMeasurable (a i j)
      (μ.prod (volume.restrict (U : Set (Fin N → ℝ)))))
    (hb : ∀ i j, ∀ᵐ z ∂μ.prod (volume.restrict (U : Set (Fin N → ℝ))), ‖a i j z‖ ≤ C)
    (v : T → energyGraph U X) (hv : MemLp v 2 μ) :
    ∃ J : T → PiLp 2 (fun _ : Fin q => SpatialL2 U), MemLp J 2 μ ∧
      ∀ i, ∀ᵐ t ∂μ, J t i =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
        fun x => ∑ j, a i j (t, x) * (v t : GradientSpace U q).snd j x := by
  simpa only [energyGradient_apply] using
    exists_Bochner_flux_of_L2_curve U a hC ha hb
      (fun t => energyGradient U X (v t)) ((energyGradient U X).comp_memLp' hv)



end HeatKernel

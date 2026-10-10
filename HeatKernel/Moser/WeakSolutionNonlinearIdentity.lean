-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.DualTimeBalance

/-! # Sign and integrability conventions for nonlinear energy identities

With positive spatial energy flux F, the time derivative of the energy is −F applied
to the energy test. Thus compact temporal testing gives integral χ' energy = integral
χ F(test). Both terms are required to be integrable. A normalized scalar test uses its
normalized primitive as the energy; centering corrections are retained.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HeatKernel

/-- An equality of regularized energy and flux integrals passes to their specified limits.
The regularized equation and both limiting statements are explicit hypotheses. -/
theorem nonlinear_energy_integral_eq_of_regularized_limits {ι : Type*} {l : Filter ι}
    [NeBot l] {A B : ι → ℝ} {a b : ℝ}
    (hA : Tendsto A l (𝓝 a)) (hB : Tendsto B l (𝓝 b)) (he : A =ᶠ[l] B) : a = b :=
  tendsto_nhds_unique hA (hB.congr' he.symm)

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.GeometricCorrectionSequence
public import Mathlib.Analysis.SpecificLimits.Basic
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter
open scoped Topology
namespace RothschildStein.G4

/-- Higher-order geometric endpoint errors imply Euclidean convergence. -/
theorem tendsto_geometric_correction_of_error {n s : ℕ}
    (z : ℕ → (Fin n → ℝ)) (y : Fin n → ℝ) (M ε : ℝ)
    (herr : ∀ j, ‖z (j+1)-y‖ ≤ M*(ε*(1/2:ℝ)^j)^(s+1)) :
    Tendsto z atTop (𝓝 y) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hp : Tendsto (fun j : ℕ => (1/2:ℝ)^j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hb : Tendsto (fun j : ℕ => M*(ε*(1/2:ℝ)^j)^(s+1)) atTop (𝓝 0) := by
    simpa using ((hp.const_mul ε).pow (s+1)).const_mul M
  exact squeeze_zero (fun j => norm_nonneg _) herr hb
end RothschildStein.G4

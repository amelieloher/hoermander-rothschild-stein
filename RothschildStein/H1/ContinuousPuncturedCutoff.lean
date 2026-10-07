-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PuncturedProductIntegrability
public import Mathlib.Analysis.Calculus.FDeriv.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter Topology
namespace RothschildStein.H1
variable {N : ℕ}

/-- Step 4: a continuous cutoff zero near the origin
regularizes a punctured continuous kernel globally. -/
theorem continuous_puncturedKernel_mul_cutoff
    {f θ : (Fin N → ℝ) → ℝ} (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    (hθ : Continuous θ) (he : θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0) :
    Continuous (fun x => f x * θ x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have hz : (fun x => f x * θ x) =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0 := by
      filter_upwards [he] with y hy
      rw [hy, mul_zero]
    exact (continuousAt_const : ContinuousAt (fun _ : Fin N → ℝ => (0 : ℝ)) 0).congr_of_eventuallyEq hz
  · exact (hf.continuousAt (isOpen_compl_singleton.mem_nhds (by simpa using hx))).mul hθ.continuousAt

end RothschildStein.H1

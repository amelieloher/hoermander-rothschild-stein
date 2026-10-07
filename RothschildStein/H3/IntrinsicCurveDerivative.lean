-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.hasIntrinsicDeriv
public import Mathlib.Analysis.ODE.Transform
public import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.H3
variable {N : ℕ}

/-- The fixed intrinsic derivative determines differentiation
at every time along an actual local integral curve, by shifting its origin.
No group exponential or Euclidean differentiability of the input is assumed
(BB Proposition 2.15, p. 82). -/
theorem hasDerivAt_comp_curve_of_intrinsic
    (Ω : Opens (Fin N → ℝ)) (X : (Fin N → ℝ) → (Fin N → ℝ))
    {f g : (Fin N → ℝ) → ℝ} (hf : hasIntrinsicDeriv Ω X f g)
    {γ : ℝ → (Fin N → ℝ)} {t : ℝ}
    (hγ : IsIntegralCurveAt γ (fun _ => X) t)
    (hmem : ∀ᶠ s in 𝓝 t, γ s ∈ (Ω : Set (Fin N → ℝ))) :
    HasDerivAt (f ∘ γ) (g (γ t)) t := by
  have hx := mem_of_mem_nhds hmem
  have hshift : IsIntegralCurveAt (fun s => γ (s + t)) (fun _ => X) 0 := by
    simpa only [sub_self, Function.comp_def] using hγ.comp_add t
  have ht : Tendsto (fun s : ℝ => s + t) (𝓝 0) (𝓝 t) := by
    simpa only [zero_add] using
      (show Continuous (fun s : ℝ => s + t) from continuous_id.add continuous_const).continuousAt
        (x := (0 : ℝ)) |>.tendsto
  have hd := (hf (γ t) hx).2 (fun s => γ (s + t))
    (by simp only [zero_add]) hshift (ht.eventually hmem)
  have he := hd.comp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp only [id_eq, sub_self])
  simpa only [Function.comp_def, sub_add_cancel, mul_one, id_eq] using he

end RothschildStein.H3

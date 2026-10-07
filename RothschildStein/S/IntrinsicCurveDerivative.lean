-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.hasIntrinsicDeriv
public import Mathlib.Analysis.ODE.Transform

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- The intrinsic derivative is the ordinary derivative along every local integral curve at every time, by translating the curve to the base time (BB Proposition 2.22, pp. 88–90). -/
theorem hasDerivAt_comp_curve_of_intrinsic_derivative
    (Ω : Opens (Fin n → ℝ)) (X : (Fin n → ℝ) → (Fin n → ℝ))
    {f g : (Fin n → ℝ) → ℝ} (hf : hasIntrinsicDeriv Ω X f g)
    (γ : ℝ → (Fin n → ℝ)) {t : ℝ}
    (hγ : IsIntegralCurveAt γ (fun _ => X) t) (hx : γ t ∈ (Ω : Set (Fin n → ℝ))) :
    HasDerivAt (fun s => f (γ s)) (g (γ t)) t := by
  let β := fun r : ℝ => γ (r+t)
  have hb : IsIntegralCurveAt β (fun _ => X) 0 := by
    simpa only [sub_self,Function.comp_def] using hγ.comp_add t
  have hβ0 : β 0 = γ t := by simp only [β,zero_add]
  have hm : ∀ᶠ r in 𝓝 (0 : ℝ),β r ∈ (Ω : Set (Fin n → ℝ)) :=
    hb.continuousAt.preimage_mem_nhds (Ω.isOpen.mem_nhds (hβ0.symm ▸ hx))
  have hd := (hf (γ t) hx).2 β hβ0 hb hm
  have ht : HasDerivAt (fun s : ℝ => s-t) 1 t := by
    simpa only [id_eq] using (hasDerivAt_id t).sub_const t
  have hd' : HasDerivAt (fun r => f (β r)) (g (γ t)) ((fun s : ℝ => s-t) t) := by
    simpa only [sub_self] using hd
  have H := hd'.scomp (h := fun s : ℝ => s-t) t ht
  simpa only [β,Function.comp_def,sub_add_cancel,one_smul] using H

end RothschildStein.S

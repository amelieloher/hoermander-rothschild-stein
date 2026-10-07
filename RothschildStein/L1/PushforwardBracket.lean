-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.Analysis.Calculus.VectorField
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.L1

/-- Brackets commute with an actual smooth coordinate pushforward.
The field agreement is a neighborhood identity, so differentiation uses
its actual derivatives (BB Proposition 10.22, p. 500). -/
theorem lieBracket_pushforward {N M : ℕ}
    (f : (Fin N → ℝ) → (Fin M → ℝ)) (x : Fin N → ℝ)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x)
    (V W : (Fin N → ℝ) → (Fin N → ℝ))
    (V' W' : (Fin M → ℝ) → (Fin M → ℝ))
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x)
    (hV' : DifferentiableAt ℝ V' (f x)) (hW' : DifferentiableAt ℝ W' (f x))
    (hVr : (fun y => fderiv ℝ f y (V y)) =ᶠ[𝓝 x] (fun y => V' (f y)))
    (hWr : (fun y => fderiv ℝ f y (W y)) =ᶠ[𝓝 x] (fun y => W' (f y))) :
    fderiv ℝ f x (VectorField.lieBracket ℝ V W x) =
      VectorField.lieBracket ℝ V' W' (f x) := by
  rw [VectorField.fderiv_apply_lieBracket hf (by simp) hW hV]
  rw [hWr.fderiv_eq,hVr.fderiv_eq]
  have hd := hf.differentiableAt (by simp)
  change fderiv ℝ (W' ∘ f) x (V x) - fderiv ℝ (V' ∘ f) x (W x) = _
  rw [fderiv_comp x hW' hd,fderiv_comp x hV' hd]
  simp only [ContinuousLinearMap.comp_apply,hVr.self_of_nhds,hWr.self_of_nhds]
  rfl
end RothschildStein.L1

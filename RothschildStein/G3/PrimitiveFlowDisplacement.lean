-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G1.MixedFlowDisplacement
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.G3

theorem primitiveFlow_displacement_le {N : ℕ} {Ω : Set (Fin N → ℝ)}
    {X : (Fin N → ℝ) → (Fin N → ℝ)} {τ B : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ)
    (hzero : Φ (x,0) = x)
    (hODE : ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x,w)) (X (Φ (x,v))) v ∧ Φ (x,v) ∈ Ω)
    (hbound : ∀ y ∈ Ω, ‖X y‖ ≤ B) {t : ℝ} (ht : t ∈ Ioo (-τ) τ) :
    ‖Φ (x,t)-x‖ ≤ B*|t| := by
  have hzeroT : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith,hτ⟩
  have hsub : uIcc 0 t ⊆ Ioo (-τ) τ := ordConnected_Ioo.uIcc_subset hzeroT ht
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v hv => (hODE v (hsub hv)).1.hasDerivWithinAt)
    (fun v hv => hbound _ (hODE v (hsub hv)).2)
    (convex_uIcc (0 : ℝ) t) left_mem_uIcc right_mem_uIcc
  simpa only [hzero,sub_zero,Real.norm_eq_abs] using hh
end RothschildStein.G3

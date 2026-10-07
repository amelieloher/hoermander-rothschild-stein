-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.Frames
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.G4

/-- Joint field-value continuity suffices for joint determinant
continuity; no parameter differentiation is involved. -/
theorem frameDet_joint_continuousOn {P ι : Type*} [TopologicalSpace P] {n : ℕ}
    {S : Set (P × (Fin n → ℝ))}
    (Z : P → ι → (Fin n → ℝ) → (Fin n → ℝ))
    (hZ : ∀ j, ContinuousOn (fun q : P × (Fin n → ℝ) => Z q.1 j q.2) S)
    (B : Fin n → ι) :
    ContinuousOn (fun q : P × (Fin n → ℝ) => frameDet (Z q.1) B q.2) S := by
  classical
  unfold frameDet
  simp only [Matrix.det_apply']
  apply continuousOn_finsetSum
  intro σ _
  apply continuousOn_const.mul
  apply continuousOn_finsetProd
  intro j _
  exact (continuous_apply (σ j)).comp_continuousOn (hZ (B j))
end RothschildStein.G4

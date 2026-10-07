-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.JointTransportedKernel
public import RothschildStein.G4.ParameterFlowSmoothness

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- The transported kernel of an actual continuous parameter flow
is jointly smooth on its actual reverse-endpoint open overlap, using the
joint smoothness of the parameter flow (BB pp. 441–443). -/
theorem actual_parameterFlow_transported_kernel_contDiffOn {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {A : Set P} {Ω : Set E} {U : Set (P × E)}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUA : U ⊆ A ×ˢ Ω)
    {Z : P × E → E} (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω))
    {τ : ℝ} (hτ : 0 < τ) (Φ : (P × E) × ℝ → E)
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ U, Φ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (p, w)) (Z (p.1, Φ (p, v))) v ∧ Φ (p, v) ∈ Ω)
    (Y : P × E → E) (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y U) :
    let S := (U ×ˢ Ioo (-τ) τ) ∩
      {q | (q.1.1, Φ (q.1, -q.2)) ∈ U}
    IsOpen S ∧ ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q => (fderiv ℝ (fun y => Φ ((q.1.1, y), q.2)) (Φ (q.1, -q.2)))
        (Y (q.1.1, Φ (q.1, -q.2)))) S := by
  exact transported_kernel_contDiffOn_of_joint_contDiff hU Φ
    (parameterFlow_contDiffOn hA hΩ hU hUA hZ hτ Φ hc hΦ) Y hY

end RothschildStein.G4

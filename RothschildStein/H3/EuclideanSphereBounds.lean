-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.EuclideanDerivativeBounds
public import RothschildStein.H3.C1FieldHomogeneity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3
variable {N : ℕ}

/-- The actual Euclidean-gradient maximum on the gauge sphere. -/
def euclideanGradientSphereBound (ν f : (Fin N → ℝ) → ℝ) : ℝ :=
  kernelSphereBound ν (fun x => ‖euclideanDifferential f x‖)

/-- C¹ scalar regularity suffices for continuity of the
Euclidean differential norm on the punctured coordinate space. -/
theorem euclideanDifferential_continuousOn {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiffOn ℝ 1 f {0}ᶜ) :
    ContinuousOn (euclideanDifferential f) {0}ᶜ :=
  (hf.continuousOn_fderiv_of_isOpen isOpen_compl_singleton le_rfl).clm_comp
    continuousOn_const

/-- The Euclidean gradient maximum is finite, nonnegative,
attained, and bounds every actual Euclidean gradient on the unit sphere. -/
theorem euclideanGradientSphereBound_properties
    {G : HomogeneousGroup N} {ν f : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) (hf : ContDiffOn ℝ 1 f {0}ᶜ) :
    0 ≤ euclideanGradientSphereBound ν f ∧
      (∃ x, ν x = 1 ∧ ‖euclideanDifferential f x‖ = euclideanGradientSphereBound ν f) ∧
      ∀ x, ν x = 1 → ‖euclideanDifferential f x‖ ≤ euclideanGradientSphereBound ν f := by
  have hp := kernelSphereBound_continuous hν (euclideanDifferential_continuousOn hf).norm
  simpa only [euclideanGradientSphereBound, abs_norm] using hp

end RothschildStein.H3

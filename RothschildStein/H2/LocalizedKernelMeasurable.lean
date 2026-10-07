-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.SingularL2Extension

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- The localized kernel vanishes outside its two cutoff variables. -/
theorem LocalKernelData.cutoffKernel_outside (Q : LocalKernelData D d) (x y : X)
    (hxy : x ∉ ball Q.z Q.R ∨ y ∉ ball Q.z Q.R) : Q.cutoffKernel x y = 0 := by
  rcases hxy with hx | hy
  · simp [LocalKernelData.cutoffKernel, localizedKernel, hx]
  · simp [LocalKernelData.cutoffKernel, localizedKernel, hy]

/-- The supported localized kernel is jointly measurable globally.
The measurable kernel class on U×U extends by zero outside that product. -/
theorem LocalKernelData.cutoffKernel_measurable (Q : LocalKernelData D d) :
    Measurable (Function.uncurry Q.cutoffKernel) := by
  let U := ball Q.z Q.R
  apply measurable_of_restrict_of_restrict_compl (isOpen_ball.measurableSet.prod isOpen_ball.measurableSet)
  · have h₁ : Measurable (fun p : U ×ˢ U => (⟨p.val.1, p.property.1⟩ : U)) :=
      (measurable_fst.comp measurable_subtype_coe).subtype_mk
    have h₂ : Measurable (fun p : U ×ˢ U => (⟨p.val.2, p.property.2⟩ : U)) :=
      (measurable_snd.comp measurable_subtype_coe).subtype_mk
    exact Q.supported_localized_singular.kernel.measurable.comp (h₁.prodMk h₂)
  · have he : ((U ×ˢ U)ᶜ).domRestrict (Function.uncurry Q.cutoffKernel) = (fun _ => (0 : ℝ)) := by
      funext p
      exact Q.cutoffKernel_outside p.val.1 p.val.2
        (not_and_or.mp p.property)
    rw [he]
    exact measurable_const

end RothschildStein.H2

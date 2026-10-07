-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PuncturedFieldHomogeneity
public import RothschildStein.H1.HomogeneousKernelIntegrability
public import RothschildStein.H1.Standing
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- A standing horizontal derivative of a punctured
C¹ kernel is continuous and homogeneous of degree β−1. -/
theorem StandingHypotheses.horizontalKernel_regular
    (H : StandingHypotheses G q) (i : Fin q) {f : (Fin N → ℝ) → ℝ} {β : ℝ}
    (hc : ContDiffOn ℝ 1 f {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ β * f x) :
    ContinuousOn (fieldDerivative (H.fields i.succ) f) {(0 : Fin N → ℝ)}ᶜ ∧
    ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      fieldDerivative (H.fields i.succ) f (G.dilate t x) =
        t ^ (β - 1) * fieldDerivative (H.fields i.succ) f x := by
  constructor
  · change ContinuousOn (fun x => fderiv ℝ f x (H.fields i.succ x)) _
    exact (hc.continuousOn_fderiv_of_isOpen isOpen_compl_singleton (by norm_num)).clm_apply
      (H.fields_smooth G i.succ).continuous.continuousOn
  · have hv : G2.IsHomogeneousField G (H.fields i.succ) 1 := by
      simpa using H.homogeneous i.succ
    intro t ht x hx
    exact fieldDerivative_punctured_homogeneity G hv hc hhom ht hx

/-- Above the critical degree, the actual horizontal
kernel derivative is locally integrable on the full group. -/
theorem StandingHypotheses.horizontalKernel_locallyIntegrable
    (H : StandingHypotheses G q) (i : Fin q) {f : (Fin N → ℝ) → ℝ} {β : ℝ}
    (hc : ContDiffOn ℝ 1 f {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ β * f x)
    (hβ : 1 - (G.homogeneousDimension : ℝ) < β) :
    MeasureTheory.LocallyIntegrable (fieldDerivative (H.fields i.succ) f) := by
  obtain ⟨hF, hh⟩ := H.horizontalKernel_regular G i hc hhom
  exact locallyIntegrable_homogeneousKernel G H.norm.gauge hF hh (by linarith)

end RothschildStein.H1

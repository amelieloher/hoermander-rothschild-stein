-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.HorizontalKernelPrincipalValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- First horizontal derivatives of a punctured C²
fundamental-degree kernel retain C¹ regularity and have degree 1−Q. -/
theorem StandingHypotheses.firstKernel_C1
    (H : StandingHypotheses G q) (j : Fin q) {Γ : (Fin N → ℝ) → ℝ}
    (hc : ContDiffOn ℝ 2 Γ {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      Γ (G.dilate t x) = t ^ (2 - (G.homogeneousDimension : ℝ)) * Γ x) :
    ContDiffOn ℝ 1 (fieldDerivative (H.fields j.succ) Γ) {(0 : Fin N → ℝ)}ᶜ ∧
    ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      fieldDerivative (H.fields j.succ) Γ (G.dilate t x) =
        t ^ (1 - (G.homogeneousDimension : ℝ)) * fieldDerivative (H.fields j.succ) Γ x := by
  constructor
  · change ContDiffOn ℝ 1 (fun x => fderiv ℝ Γ x (H.fields j.succ x)) _
    exact (hc.fderiv_of_isOpen isOpen_compl_singleton (by norm_num)).clm_apply
      ((H.fields_smooth G j.succ).of_le (by simp)).contDiffOn
  · have hh := (H.horizontalKernel_regular G j (hc.of_le (by norm_num)) hhom).2
    have hd : (2 - (G.homogeneousDimension : ℝ)) - 1 = 1 - (G.homogeneousDimension : ℝ) := by ring
    simpa only [hd] using hh

end RothschildStein.H1

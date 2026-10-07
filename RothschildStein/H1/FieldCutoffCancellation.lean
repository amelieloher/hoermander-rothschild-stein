-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.FieldCutoffSupport
public import RothschildStein.H1.FieldCutoffScaling
public import RothschildStein.H1.DilatedCutoffTest
public import RothschildStein.H1.Integration
public import RothschildStein.G2.HomogeneousType

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace MeasureTheory
open scoped Topology
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The standing field derivative has zero pairing against
a difference of dilated cutoffs at precisely C¹ kernel regularity. -/
theorem StandingHypotheses.integral_field_cutoffDifference_zero
    (H : StandingHypotheses G q) (i : Fin (q + 1))
    {f θ : (Fin N → ℝ) → ℝ}
    (hc : ContDiffOn ℝ 1 f {(0 : Fin N → ℝ)}ᶜ)
    (hscale : ∀ s : ℝ, 0 < s → ∀ x, x ≠ 0 →
      f (G.dilate s x) = s ^ ((if i = 0 then 2 else 1) - (G.homogeneousDimension : ℝ)) * f x)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hs : HasCompactSupport θ)
    (he : θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t) :
    ∫ x, fieldDerivative (H.fields i) f x * (θ (G.dilate s x) - θ (G.dilate t x)) = 0 := by
  let U : Opens (Fin N → ℝ) := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  obtain ⟨ψ, hψ⟩ := exists_dilatedCutoffDifference_test G hθ hs he hs0 ht0
  have hψf : (ψ : (Fin N → ℝ) → ℝ) =
      fun x => θ (G.dilate s x) - θ (G.dilate t x) := funext hψ
  have h := H.integral_field_test G U i f hc ψ
  have hθs : ContDiff ℝ (⊤ : ℕ∞) (fun x => θ (G.dilate s x)) := hθ.comp (G2.contDiff_dilate G s)
  have hθt : ContDiff ℝ (⊤ : ℕ∞) (fun x => θ (G.dilate t x)) := hθ.comp (G2.contDiff_dilate G t)
  have hd : fieldDerivative (H.fields i) (fun x => θ (G.dilate s x) - θ (G.dilate t x)) =
      fun x => fieldDerivative (H.fields i) (fun y => θ (G.dilate s y)) x -
        fieldDerivative (H.fields i) (fun y => θ (G.dilate t y)) x := by
    funext x
    unfold fieldDerivative
    change fderiv ℝ ((fun y => θ (G.dilate s y)) - (fun y => θ (G.dilate t y))) x _ = _
    rw [fderiv_sub ((hθs.differentiable (by simp)).differentiableAt)
      ((hθt.differentiable (by simp)).differentiableAt)]
    rfl
  change (∫ x in {(0 : Fin N → ℝ)}ᶜ, fieldDerivative (H.fields i) f x * ψ x) =
    -(∫ x in {(0 : Fin N → ℝ)}ᶜ, f x * fieldDerivative (H.fields i) ψ x) at h
  rw [G2.volume_restrict_punctured G, hψf, hd] at h
  have hiS := integrable_mul_fieldDerivative_cutoff (H.fields i) (H.fields_smooth G i)
    hc.continuousOn hθs (hasCompactSupport_comp_dilate G hs hs0)
    (cutoff_comp_dilate_eventually_one G he s)
  have hiT := integrable_mul_fieldDerivative_cutoff (H.fields i) (H.fields_smooth G i)
    hc.continuousOn hθt (hasCompactSupport_comp_dilate G hs ht0)
    (cutoff_comp_dilate_eventually_one G he t)
  have hS := integral_homogeneous_field_cutoff_dilate G (H.homogeneous i) hscale hθ hs0
  have hT := integral_homogeneous_field_cutoff_dilate G (H.homogeneous i) hscale hθ ht0
  change (∫ x, f x * fieldDerivative (H.fields i) (fun y => θ (G.dilate s y)) x) =
    ∫ x, f x * fieldDerivative (H.fields i) θ x at hS
  change (∫ x, f x * fieldDerivative (H.fields i) (fun y => θ (G.dilate t y)) x) =
    ∫ x, f x * fieldDerivative (H.fields i) θ x at hT
  simp_rw [mul_sub] at h
  rw [integral_sub hiS hiT, hS, hT, sub_self, neg_zero] at h
  simpa only [mul_sub] using h

end RothschildStein.H1

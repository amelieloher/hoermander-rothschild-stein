-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.DilatedCutoffTest
public import RothschildStein.H1.LocalDifferentialPairing
public import RothschildStein.H1.DifferentialSupport
public import RothschildStein.H1.DifferentialSubtract
public import RothschildStein.H1.HomogeneousTransposePairing
public import RothschildStein.G2.HomogeneousType

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace MeasureTheory
open scoped Topology BigOperators
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 2: the integral of a homogeneous derivative against
a difference of two dilated cutoffs vanishes. This uses precisely
finite local regularity of the original function, not global smoothness
(BB Corollary 6.31, p. 280). -/
theorem integral_homogeneous_cutoffDifference_zero
    (P : SmoothDifferentialOperator N) {k : ℝ} (hk : 0 < k) (hP : P.IsHomogeneous G k)
    {f θ : (Fin N → ℝ) → ℝ} (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    (hreg : ∀ a ∈ P.indices, ContDiffOn ℝ (∑ j, a j : ℕ) f {(0 : Fin N → ℝ)}ᶜ)
    (hscale : ∀ s : ℝ, 0 < s → ∀ x, x ≠ 0 →
      f (G.dilate s x) = s ^ (k - (G.homogeneousDimension : ℝ)) * f x)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hs : HasCompactSupport θ)
    (he : θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t) :
    ∫ x, P.apply f x * (θ (G.dilate s x) - θ (G.dilate t x)) = 0 := by
  let U : Opens (Fin N → ℝ) := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  obtain ⟨ψ, hψ⟩ := exists_dilatedCutoffDifference_test G hθ hs he hs0 ht0
  have hψf : (ψ : (Fin N → ℝ) → ℝ) =
      fun x => θ (G.dilate s x) - θ (G.dilate t x) := funext hψ
  have h := integral_differentialOperator_mul_test U P f hreg ψ
  change (∫ x in {(0 : Fin N → ℝ)}ᶜ, P.apply f x * ψ x) =
    ∫ x in {(0 : Fin N → ℝ)}ᶜ, f x * G2.differentialTranspose P ψ x at h
  have hθs : ContDiff ℝ (⊤ : ℕ∞) (fun x => θ (G.dilate s x)) := hθ.comp (G2.contDiff_dilate G s)
  have hθt : ContDiff ℝ (⊤ : ℕ∞) (fun x => θ (G.dilate t x)) := hθ.comp (G2.contDiff_dilate G t)
  rw [G2.volume_restrict_punctured G, hψf, differentialTranspose_sub P hθs hθt] at h
  have hiS := integrable_mul_differentialTranspose_cutoff G P hk hP hf
    hθs (hasCompactSupport_comp_dilate G hs hs0)
    (cutoff_comp_dilate_eventually_one G he s)
  have hiT := integrable_mul_differentialTranspose_cutoff G P hk hP hf
    hθt (hasCompactSupport_comp_dilate G hs ht0)
    (cutoff_comp_dilate_eventually_one G he t)
  have hS := integral_homogeneous_transpose_dilate G P hP hscale hθ hs0
  have hT := integral_homogeneous_transpose_dilate G P hP hscale hθ ht0
  change (∫ x, f x * G2.differentialTranspose P (fun y => θ (G.dilate s y)) x) =
    ∫ x, f x * G2.differentialTranspose P θ x at hS
  change (∫ x, f x * G2.differentialTranspose P (fun y => θ (G.dilate t y)) x) =
    ∫ x, f x * G2.differentialTranspose P θ x at hT
  simp_rw [mul_sub] at h
  rw [integral_sub hiS hiT, hS, hT, sub_self] at h
  simpa only [mul_sub] using h

end RothschildStein.H1

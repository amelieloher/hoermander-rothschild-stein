-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.FundamentalFirstDerivative
public import RothschildStein.H1.CutoffCoefficientIndependence
public import RothschildStein.H1.PrincipalValueUniformLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter Topology
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N) (H : StandingHypotheses G q)

/-- The actual second derivative representation, with
BB's ball-integral coefficient and the full drift operator Lu. -/
theorem FundamentalKernel.secondDerivative_representation (K : FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) (i j : Fin q)
    {η u : (Fin N → ℝ) → ℝ} {R : ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hsη : HasCompactSupport η)
    (heη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    (hR : 0 < R) (hout : ∀ w, R ≤ H.norm w → η w = 0) (hbη : ∀ w, ‖η w‖ ≤ 1)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hsu : HasCompactSupport u) :
    fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) u) =
      (fun x => principalValueConvolution G H.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K))
        (sumSquaresWithDrift H.fields u) x + sumSquaresWithDrift H.fields u x *
        (∫ w in {w | H.norm w ≤ R}, fieldDerivative (H.fields i.succ)
          (fun v => fieldDerivative (H.fields j.succ) K v * (1 - η v)) w)) := by
  let ut : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) := ⟨u, hu, hsu, subset_univ _⟩
  let ψ := sumSquaresTest ⊤ H.fields (fun k => (H.fields_smooth G k).contDiffOn) ut
  have heψ : (ψ : (Fin N → ℝ) → ℝ) = sumSquaresWithDrift H.fields u :=
    funext fun x => sumSquaresTest_apply ⊤ H.fields (fun k => (H.fields_smooth G k).contDiffOn) ut x
  obtain ⟨hf, hhom⟩ := H.firstKernel_C1 G j (K.smooth_off_zero.of_le (by simp)) K.homogeneous
  have he := H.fieldDerivative_criticalPotential_ballCoefficient G i hf hhom hη hsη heη hR hout hbη ψ.contDiff ψ.hasCompactSupport
  rw [heψ, ← K.firstDerivative_representation G H hQ j hu hsu] at he
  exact he

/-- actual second kernel derivatives have vanishing
shell integrals for the fixed homogeneous norm. -/
theorem FundamentalKernel.secondDerivative_shellCancellation (K : FundamentalKernel G H)
    (i j : Fin q) : HasVanishingShellIntegrals H.norm
      (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) := by
  obtain ⟨hf, hh⟩ := H.firstKernel_C1 G j (K.smooth_off_zero.of_le (by simp)) K.homogeneous
  exact H.vanishingShellIntegrals_fieldDerivative G i.succ H.norm.gauge hf (by simpa using hh)

/-- The truncated second kernel potentials converge
uniformly on the whole group to their actual principal value. -/
theorem FundamentalKernel.secondDerivative_uniformPrincipalValue (K : FundamentalKernel G H)
    (i j : Fin q) {u : (Fin N → ℝ) → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hsu : HasCompactSupport u) :
    TendstoUniformly
      (fun ε => principalValueTruncation G H.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K))
        (sumSquaresWithDrift H.fields u) ε)
      (principalValueConvolution G H.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K))
        (sumSquaresWithDrift H.fields u)) (nhdsWithin 0 (Ioi 0)) := by
  let ut : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) := ⟨u, hu, hsu, subset_univ _⟩
  let ψ := sumSquaresTest ⊤ H.fields (fun k => (H.fields_smooth G k).contDiffOn) ut
  have heψ : (ψ : (Fin N → ℝ) → ℝ) = sumSquaresWithDrift H.fields u :=
    funext fun x => sumSquaresTest_apply ⊤ H.fields (fun k => (H.fields_smooth G k).contDiffOn) ut x
  obtain ⟨hf, hh⟩ := H.firstKernel_C1 G j (K.smooth_off_zero.of_le (by simp)) K.homogeneous
  obtain ⟨hF, hhF⟩ := H.horizontalKernel_regular G i hf hh
  have hscale : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K) (G.dilate t x) =
        t ^ (-(G.homogeneousDimension : ℝ)) * fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K) x := by
    simpa only [show (1 - (G.homogeneousDimension : ℝ)) - 1 = -(G.homogeneousDimension : ℝ) by ring] using hhF
  have ht := tendstoUniformly_principalValueTruncation G H.norm.gauge hF hscale
    (K.secondDerivative_shellCancellation G H i j) (ψ.contDiff.of_le (by simp)) ψ.hasCompactSupport
  rw [heψ] at ht
  exact ht

end RothschildStein.H1

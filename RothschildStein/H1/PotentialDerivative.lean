-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.SupercriticalPotentialDerivative
public import RothschildStein.H1.CriticalPotentialDerivative
public import RothschildStein.H1.CriticalCutoffCoefficient
public import RothschildStein.H1.GaugeCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Differentiating a supercritical homogeneous
potential under the integral, with no regularization data as premises. -/
theorem StandingHypotheses.fieldDerivative_homogeneousPotential
    (H : StandingHypotheses G q) (i : Fin q)
    {f ψ : (Fin N → ℝ) → ℝ} {β : ℝ}
    (hf : ContDiffOn ℝ 1 f {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ β * f x)
    (hβ : 1 - (G.homogeneousDimension : ℝ) < β)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hsψ : HasCompactSupport ψ) :
    fieldDerivative (H.fields i.succ) (G2.groupConvolution G ψ f) =
      G2.groupConvolution G ψ (fieldDerivative (H.fields i.succ) f) := by
  obtain ⟨η, R, hη, hsη, heη, hR, hout, hb⟩ := exists_compactGaugeCutoff G H.norm.gauge
  exact H.fieldDerivative_supercriticalPotential G i hf hhom hβ hη hsη heη hR hout hb hψ hsψ

/-- The critical potential derivative is principal
value convolution plus the source ball-integral cutoff coefficient. -/
theorem StandingHypotheses.fieldDerivative_criticalPotential_ballCoefficient
    (H : StandingHypotheses G q) (i : Fin q)
    {f η ψ : (Fin N → ℝ) → ℝ} {R : ℝ}
    (hf : ContDiffOn ℝ 1 f {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      f (G.dilate t x) = t ^ (1 - (G.homogeneousDimension : ℝ)) * f x)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hsη : HasCompactSupport η)
    (heη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    (hR : 0 < R) (hηout : ∀ w, R ≤ H.norm w → η w = 0)
    (hbη : ∀ w, ‖η w‖ ≤ 1)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hsψ : HasCompactSupport ψ) :
    fieldDerivative (H.fields i.succ) (G2.groupConvolution G ψ f) =
      (fun x => principalValueConvolution G H.norm (fieldDerivative (H.fields i.succ) f) ψ x +
        ψ x * (∫ w in {w | H.norm w ≤ R},
          fieldDerivative (H.fields i.succ) (fun v => f v * (1 - η v)) w)) := by
  have he := H.fieldDerivative_criticalPotential G i hf hhom hη hsη heη hR hηout hbη hψ hsψ
  rw [criticalCutoffCoefficient_eq_ballIntegral G H.norm.gauge (H.fields i.succ)
    (H.fields_smooth G i.succ) hf hη hsη heη hηout] at he
  exact he

end RothschildStein.H1

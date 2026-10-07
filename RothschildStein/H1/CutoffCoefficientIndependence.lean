-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PotentialDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology TopologicalSpace
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The source critical coefficient is independent of
both the smooth cutoff and its enclosing gauge-ball radius. -/
theorem StandingHypotheses.criticalCutoffCoefficient_independent
    (H : StandingHypotheses G q) (i : Fin q)
    {f η₁ η₂ : (Fin N → ℝ) → ℝ} {R₁ R₂ : ℝ}
    (hf : ContDiffOn ℝ 1 f {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      f (G.dilate t x) = t ^ (1 - (G.homogeneousDimension : ℝ)) * f x)
    (hη₁ : ContDiff ℝ (⊤ : ℕ∞) η₁) (hs₁ : HasCompactSupport η₁)
    (he₁ : η₁ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    (hR₁ : 0 < R₁) (hout₁ : ∀ w, R₁ ≤ H.norm w → η₁ w = 0) (hb₁ : ∀ w, ‖η₁ w‖ ≤ 1)
    (hη₂ : ContDiff ℝ (⊤ : ℕ∞) η₂) (hs₂ : HasCompactSupport η₂)
    (he₂ : η₂ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    (hR₂ : 0 < R₂) (hout₂ : ∀ w, R₂ ≤ H.norm w → η₂ w = 0) (hb₂ : ∀ w, ‖η₂ w‖ ≤ 1) :
    (∫ w in {w | H.norm w ≤ R₁}, fieldDerivative (H.fields i.succ) (fun v => f v * (1 - η₁ v)) w) =
    (∫ w in {w | H.norm w ≤ R₂}, fieldDerivative (H.fields i.succ) (fun v => f v * (1 - η₂ v)) w) := by
  let U : Opens (Fin N → ℝ) := ⟨univ, isOpen_univ⟩
  obtain ⟨ψ, W, _, hKW, hOne, _⟩ := exists_test_eq_one_near_compact U
    (isCompact_singleton (x := (0 : Fin N → ℝ))) (subset_univ _)
  have hψ0 : ψ (0 : Fin N → ℝ) = 1 := hOne 0 (hKW (mem_singleton 0))
  have h₁ := H.fieldDerivative_criticalPotential_ballCoefficient G i hf hhom hη₁ hs₁ he₁ hR₁ hout₁ hb₁ ψ.contDiff ψ.hasCompactSupport
  have h₂ := H.fieldDerivative_criticalPotential_ballCoefficient G i hf hhom hη₂ hs₂ he₂ hR₂ hout₂ hb₂ ψ.contDiff ψ.hasCompactSupport
  have he := congrFun (h₁.symm.trans h₂) (0 : Fin N → ℝ)
  change principalValueConvolution G H.norm (fieldDerivative (H.fields i.succ) f) ψ 0 + ψ 0 * _ =
    principalValueConvolution G H.norm (fieldDerivative (H.fields i.succ) f) ψ 0 + ψ 0 * _ at he
  rw [hψ0, one_mul, one_mul] at he
  exact add_left_cancel he

end RothschildStein.H1

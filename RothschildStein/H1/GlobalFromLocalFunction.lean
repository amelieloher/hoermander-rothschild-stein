-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.LocalizedKernelData
public import RothschildStein.H1.GlobalFromLocalKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Construct the global homogeneous fundamental function
from a local integrable fundamental function on any neighborhood of zero.
The local distribution-to-function theorem supplies the required input
(BB pp. 263–266). -/
theorem StandingHypotheses.exists_globalFundamental_of_localFunction
    (H : StandingHypotheses G q) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    {γ : (Fin N → ℝ) → ℝ} (hγ : IntegrableOn γ (Ω : Set (Fin N → ℝ)) volume)
    (hcγ : ContDiffOn ℝ (⊤ : ℕ∞) γ ((Ω : Set (Fin N → ℝ)) ∩ {(0 : Fin N → ℝ)}ᶜ))
    (hlocal : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞),
      (∫ x, γ x * sumSquaresWithDriftTranspose H.fields ψ x) = ψ 0) :
    ∃ F : (Fin N → ℝ) → ℝ,
      LocallyIntegrable F ∧ ContDiffOn ℝ (⊤ : ℕ∞) F ({(0 : Fin N → ℝ)}ᶜ) ∧
      (∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, F x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0) ∧
      (∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
        F (G.dilate t x) = t ^ (2 - (G.homogeneousDimension : ℝ)) * F x) := by
  obtain ⟨Γ, E, hi, hs, hc, hsmE, hsE, hzE, hscaled⟩ :=
    H.exists_localizedKernelData G Ω h0 hγ hcγ hlocal
  have he : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, Γ x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0 + ∫ x, E x * φ x := by
    intro φ hφ hcomp
    simpa only [scaledFundamentalKernel, scaledErrorKernel, one_pow, inv_one, one_mul,
      G2.dilate_one] using hscaled 1 (by norm_num) φ hφ hcomp
  exact H.exists_globalFundamental_of_localKernel G hQ hi.locallyIntegrable hs hc hsmE hsE hzE he

end RothschildStein.H1

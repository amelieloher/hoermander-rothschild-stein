-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ScaledKernelSupport
public import RothschildStein.H1.SmoothCompactRepresentative
public import RothschildStein.H1.FundamentalDictionary
public import RothschildStein.H1.ReversedOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open TopologicalSpace Set MeasureTheory
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Construct the compact smooth correction from the complete
local kernel identity. Its right hand side is E₂−E₁, not zero
(BB p. 266; function-level regularity argument). -/
theorem StandingHypotheses.exists_localSmoothCorrection
    (H : StandingHypotheses G q)
    {Γ E : (Fin N → ℝ) → ℝ} (hΓ : LocallyIntegrable Γ)
    (hsΓ : HasCompactSupport Γ) (hcΓ : ContinuousOn Γ ({(0 : Fin N → ℝ)}ᶜ))
    (hE : ContDiff ℝ (⊤ : ℕ∞) E)
    (hlocal : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, Γ x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0 + ∫ x, E x * φ x) :
    ∃ ω : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ω ∧ HasCompactSupport ω ∧
      ∀ x ≠ 0, ω x = scaledFundamentalKernel G 2 Γ x - Γ x := by
  let u := fun x => scaledFundamentalKernel G 2 Γ x - Γ x
  let g := fun x => scaledErrorKernel G 2 E x - E x
  have hl : LocallyIntegrable (scaledFundamentalKernel G 2 Γ) :=
    locallyIntegrable_scaledFundamentalKernel G hΓ (by norm_num)
  have hs : HasCompactSupport u :=
    (hasCompactSupport_scaledFundamentalKernel G hsΓ (by norm_num : (0 : ℝ) < 2)).sub hsΓ
  have hi : Integrable u := integrable_of_locallyIntegrable_compact (hl.sub hΓ) hs
  have hc : ContinuousOn u ({(0 : Fin N → ℝ)}ᶜ) :=
    (continuousOn_scaledFundamentalKernel G hcΓ (by norm_num : (0 : ℝ) < 2)).sub hcΓ
  have hscaledE : ContDiff ℝ (⊤ : ℕ∞) (scaledErrorKernel G 2 E) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => ((2 : ℝ) ^ G.homogeneousDimension)⁻¹ *
      E (G.dilate (2 : ℝ)⁻¹ x))
    exact (hE.comp (G2.contDiff_dilate G (2 : ℝ)⁻¹)).const_smul
      (((2 : ℝ) ^ G.homogeneousDimension)⁻¹)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hscaledE.sub hE
  have heq : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * sumSquaresWithDriftTranspose H.fields φ x) = ∫ x, g x * φ x := by
    intro φ hφ hcompact
    let φtest : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) :=
      ⟨φ, hφ, hcompact, subset_univ _⟩
    let ψ := sumSquaresWithDriftTransposeTest ⊤ H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) φtest
    have hp : (ψ : (Fin N → ℝ) → ℝ) = sumSquaresWithDriftTranspose H.fields φ :=
      funext (H.transposeTest_apply G ⊤ φtest)
    have hi1 : Integrable (fun x => Γ x * sumSquaresWithDriftTranspose H.fields φ x) :=
      hΓ.integrable_smul_right_of_hasCompactSupport
      (hp ▸ ψ.contDiff.continuous) (hp ▸ ψ.hasCompactSupport)
    have hi2 : Integrable (fun x => scaledFundamentalKernel G 2 Γ x *
        sumSquaresWithDriftTranspose H.fields φ x) :=
      hl.integrable_smul_right_of_hasCompactSupport
      (hp ▸ ψ.contDiff.continuous) (hp ▸ ψ.hasCompactSupport)
    have hEloc : LocallyIntegrable E volume := hE.continuous.locallyIntegrable
    have he1 : Integrable (fun x => E x * φ x) :=
      hEloc.integrable_smul_right_of_hasCompactSupport
      hφ.continuous hcompact
    have hE2loc : LocallyIntegrable (scaledErrorKernel G 2 E) volume :=
      hscaledE.continuous.locallyIntegrable
    have he2 : Integrable (fun x => scaledErrorKernel G 2 E x * φ x) :=
      hE2loc.integrable_smul_right_of_hasCompactSupport
      hφ.continuous hcompact
    have h2 := scaled_pairing_identity G (sumSquaresWithDriftTranspose H.fields)
      (H.transpose_homogeneous G) Γ E hlocal (by norm_num : (0 : ℝ) < 2) φ hφ hcompact
    have h1 := hlocal φ hφ hcompact
    change (∫ x, (scaledFundamentalKernel G 2 Γ x - Γ x) *
      sumSquaresWithDriftTranspose H.fields φ x) =
      ∫ x, (scaledErrorKernel G 2 E x - E x) * φ x
    simp_rw [sub_mul]
    rw [integral_sub hi2 hi1, integral_sub he2 he1, h2, h1]
    ring
  obtain ⟨ω, hsm, hsω, _, heω⟩ := H.exists_smoothCompact_correction G g u hi hs hc hg heq
  exact ⟨ω, hsm, hsω, fun x hx => (heω hx).symm⟩

end RothschildStein.H1

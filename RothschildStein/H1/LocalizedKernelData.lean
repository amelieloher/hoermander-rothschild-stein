-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.CutoffPairing
public import RothschildStein.H1.NestedCutoffs
public import RothschildStein.H1.KernelScaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- A local integrable fundamental function produces compact
kernel and error data with the full scaled pairing identity. The inputs
are function data; no distribution regularity is assumed implicitly
(BB (6.22)–(6.26), p. 265). -/
theorem StandingHypotheses.exists_localizedKernelData
    (H : StandingHypotheses G q) (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    {γ : (Fin N → ℝ) → ℝ} (hγ : IntegrableOn γ (Ω : Set (Fin N → ℝ)) volume)
    (hcγ : ContDiffOn ℝ (⊤ : ℕ∞) γ ((Ω : Set (Fin N → ℝ)) ∩ {(0 : Fin N → ℝ)}ᶜ))
    (hlocal : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞),
      (∫ x, γ x * sumSquaresWithDriftTranspose H.fields ψ x) = ψ 0) :
    ∃ Γ E : (Fin N → ℝ) → ℝ,
      Integrable Γ ∧ HasCompactSupport Γ ∧
      ContDiffOn ℝ (⊤ : ℕ∞) Γ ({(0 : Fin N → ℝ)}ᶜ) ∧
      ContDiff ℝ (⊤ : ℕ∞) E ∧ HasCompactSupport E ∧ E =ᶠ[𝓝 (0 : Fin N → ℝ)] 0 ∧
      (∀ s : ℝ, 0 < s → ∀ φ : (Fin N → ℝ) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, scaledFundamentalKernel G s Γ x * sumSquaresWithDriftTranspose H.fields φ x) =
          φ 0 + ∫ x, scaledErrorKernel G s E x * φ x) := by
  obtain ⟨η₁, η₂, he₂, he₁, _, _⟩ := exists_nestedKernelCutoffs Ω h0
  let Γ := fun x => γ x * η₁ x
  let E := fun x => sumSquaresWithDrift H.fields Γ x * (1 - η₂ x)
  have hlγ : LocallyIntegrableOn γ (Ω : Set (Fin N → ℝ)) volume :=
    hγ.locallyIntegrableOn
  have hi : Integrable Γ := S.integrable_mul_test Ω hlγ η₁
  have hs : HasCompactSupport Γ := η₁.hasCompactSupport.mul_left
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({(0 : Fin N → ℝ)}ᶜ) :=
    contDiffOn_localizedKernel Ω hcγ η₁
  let U : Opens (Fin N → ℝ) := ⟨{(0 : Fin N → ℝ)}ᶜ, isOpen_compl_singleton⟩
  have hE : ContDiff ℝ (⊤ : ℕ∞) E :=
    contDiff_localizedError (H.contDiffOn_operator G U hc) η₂.contDiff he₂
  have hsE : HasCompactSupport E := hasCompactSupport_localizedError H.fields hs η₂
  have hzE : E =ᶠ[𝓝 (0 : Fin N → ℝ)] 0 :=
    localizedError_eventually_zero (sumSquaresWithDrift H.fields Γ) η₂ he₂
  have hbase : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, Γ x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0 + ∫ x, E x * φ x :=
    H.localizedKernel_pairing G Ω hlγ hcγ η₁ η₂ he₁ he₂ hlocal
  refine ⟨Γ, E, hi, hs, hc, hE, hsE, hzE, ?_⟩
  intro s hspos φ hφ hcompact
  exact scaled_pairing_identity G (sumSquaresWithDriftTranspose H.fields)
    (H.transpose_homogeneous G) Γ E hbase hspos φ hφ hcompact

end RothschildStein.H1

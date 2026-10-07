-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ConvolutionConvergence
public import RothschildStein.H3.ConvolutionLocalSolution
public import RothschildStein.H1.Standing
public import RothschildStein.G2.ConvolutionSmooth

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology
open G2

/-- The fundamental-kernel convolution is a local Sobolev solution when
the smooth approximants satisfy the stated jet estimates and equation
identities. Local integrability and convergence follow from the kernel
bounds and group mollification. -/
theorem actual_convolution_of_jet_estimates {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    {α : ℝ} (K : (Fin n → ℝ) → ℝ) (hK : PositiveType G α K)
    (ν : HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (Ω : Opens (Fin n → ℝ)) (hΩ : (Ω : Set (Fin n → ℝ)) = {x | ν x < ρ₂})
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate p r]
    (f : ℕ → (Fin n → ℝ) → ℝ) (F : (Fin n → ℝ) → ℝ)
    (hF : MemLp F p volume)
    (hfs : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) (hfc : ∀ j, HasCompactSupport (f j))
    (hsF : ∀ᵐ y ∂volume, ρ₁ ≤ ν y → F y = 0)
    (hsf : ∀ j, ∀ᵐ y ∂volume, ρ₁ ≤ ν y → f j y = 0)
    (hft : Tendsto (fun j => eLpNorm (f j-F) p volume) atTop (𝓝 0))
    (C : List (Fin (q+1)) → ℝ) (hC : ∀ I ∈ wordFamily driftWeight 2, 0 ≤ C I)
    (hdiff : ∀ I ∈ wordFamily driftWeight 2, ∀ j l,
      eLpNorm (wordDerivative H.fields I (groupConvolution G (f j) K)-
        wordDerivative H.fields I (groupConvolution G (f l) K)) p (volume.restrict (Ω : Set (Fin n → ℝ))) ≤
          ENNReal.ofReal (C I)*eLpNorm (f j-f l) p volume)
    (hbound : ∀ I ∈ wordFamily driftWeight 2, ∀ j,
      eLpNorm (wordDerivative H.fields I (groupConvolution G (f j) K)) p
        (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ ENNReal.ofReal (C I)*eLpNorm (f j) p volume)
    (heq : ∀ j (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)),
      (∫ x in (Ω : Set (Fin n → ℝ)), f j x*ψ x) =
        ∫ x in (Ω : Set (Fin n → ℝ)), groupConvolution G (f j) K x *
          sumSquaresWithDriftTranspose H.fields ψ x) :
    memSobolevX driftWeight H.fields Ω 2 p (groupConvolution G F K) ∧
      ∃ D : WeakDriftOperatorData H.fields Ω p (groupConvolution G F K),
        D.operator =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] F ∧
        ∀ I ∈ wordFamily driftWeight 2, weakWordENorm H.fields Ω I p (groupConvolution G F K) ≤
          ENNReal.ofReal (C I)*eLpNorm F p volume := by
  have hf : ∀ j, MemLp (f j) p volume :=
    fun j => (hfs j).continuous.memLp_of_hasCompactSupport (hfc j)
  have hv : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (groupConvolution G (f j) K) :=
    fun j => contDiff_groupConvolution_left G (hfs j) (hfc j) (hK.locallyIntegrable ν.gauge)
  have hconv := hK.local_convolution_tendsto ν h1 hsym hρ₁ hρ₂ Fact.out f hF hf hsF hsf hft
  rw [← hΩ] at hconv
  have hj : ∀ I ∈ wordFamily driftWeight 2, ∀ j,
      MemLp (wordDerivative H.fields I (groupConvolution G (f j) K)) p
        (volume.restrict (Ω : Set (Fin n → ℝ))) := by
    intro I hI j
    apply lt_of_le_of_lt (hbound I hI j)
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hf j).eLpNorm_lt_top
  exact local_solution_of_convolution_estimates Ω H.fields
    (fun i => (H.fields_smooth G i).contDiffOn) p r f
    (fun j => groupConvolution G (f j) K) F (groupConvolution G F K)
    hf hF (fun j => (hv j).contDiffOn) hconv.2.1 hconv.1 hj hft hconv.2.2 C hC hdiff hbound heq

end RothschildStein.H3

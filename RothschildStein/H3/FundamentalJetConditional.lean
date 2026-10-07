-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalGlobalConditional
public import RothschildStein.H3.FundamentalConvolutionWeakEquation
public import RothschildStein.H3.ConvolutionGlobalSecond
public import RothschildStein.H3.QuasiballOriginFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology
open G2

/-- The actual convolution solves the equation on every ball
and has the complete global second norm bound. Both limits use the same
input function. The actual H1 fundamental kernel proves the smooth-approximant
equations and its positive-type properties; only the jet estimates remain inputs. -/
theorem convolution_local_and_global_of_fundamental_jet_estimates {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H)
    (ν : HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    {ρ : ℝ} (hρ : 0 < ρ)
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate p r]
    (f : ℕ → (Fin n → ℝ) → ℝ) (F : (Fin n → ℝ) → ℝ)
    (hF : MemLp F p volume)
    (hfs : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) (hfc : ∀ j, HasCompactSupport (f j))
    (hsF : ∀ᵐ y ∂volume, ρ ≤ ν y → F y = 0)
    (hsf : ∀ j, ∀ᵐ y ∂volume, ρ ≤ ν y → f j y = 0)
    (hft : Tendsto (fun j => eLpNorm (f j-F) p volume) atTop (𝓝 0))
    (C : ℝ → List (Fin (q+1)) → ℝ)
    (hC : ∀ R : ℝ, 0 < R → ∀ I ∈ wordFamily driftWeight 2, 0 ≤ C R I)
    (hdiff : ∀ R : ℝ, 0 < R → ∀ I ∈ wordFamily driftWeight 2, ∀ j l,
      eLpNorm (wordDerivative H.fields I (groupConvolution G (f j) K)-
        wordDerivative H.fields I (groupConvolution G (f l) K)) p
        (volume.restrict (quasiballDomain G ν 0 R : Set (Fin n → ℝ))) ≤
          ENNReal.ofReal (C R I)*eLpNorm (f j-f l) p volume)
    (hbound : ∀ R : ℝ, 0 < R → ∀ I ∈ wordFamily driftWeight 2, ∀ j,
      eLpNorm (wordDerivative H.fields I (groupConvolution G (f j) K)) p
        (volume.restrict (quasiballDomain G ν 0 R : Set (Fin n → ℝ))) ≤
          ENNReal.ofReal (C R I)*eLpNorm (f j) p volume)
    (C₉ : ℝ) (hC₉ : 0 ≤ C₉)
    (hdiff₉ : ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 → ∀ j l,
      eLpNorm (wordDerivative H.fields I (groupConvolution G (f j) K)-
        wordDerivative H.fields I (groupConvolution G (f l) K)) p volume ≤
          ENNReal.ofReal C₉*eLpNorm (f j-f l) p volume)
    (hbound₉ : ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 → ∀ j,
      eLpNorm (wordDerivative H.fields I (groupConvolution G (f j) K)) p volume ≤
        ENNReal.ofReal C₉*eLpNorm (f j) p volume) :
    ConvolutionLocalSolutions G H ν p F K C ∧
      driftSecondWeakENorm H.fields ⊤ p (groupConvolution G F K) ≤
        (driftSecondWordFamily q).card * ENNReal.ofReal C₉ * eLpNorm F p volume := by
  have hK : PositiveType G 2 K := ⟨by norm_num, K.smooth_off_zero, K.homogeneous⟩
  refine ⟨?_,(global_second_of_convolution_estimates G H K hK ν h1 hsym hρ
    p r f F hF hfs hfc hsF hsf hft C₉ hC₉ hdiff₉ hbound₉).2⟩
  intro R hR
  exact actual_convolution_of_jet_estimates G H K hK ν h1 hsym hρ hR
    (quasiballDomain G ν 0 R) (quasiballDomain_origin_set G ν R)
    p r f F hF hfs hfc hsF hsf hft (C R) (hC R hR) (hdiff R hR) (hbound R hR) (fun j ψ => fundamental_convolution_weak_equation G H K _ (f j) (hfs j) (hfc j) ψ)

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalInputWeakJet
public import RothschildStein.H3.RelCompactConvolutionConvergence
public import RothschildStein.H3.LocalConvolutionIntegrability
public import RothschildStein.H3.CauchyEstimateTransfer
public import RothschildStein.H3.LpEstimateLimit
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

/-- A uniform global second-jet estimate gives a global Lp
weak jet of the actual convolution. Input convergence is only local;
global Lp membership of the convolution is not an input or conclusion. -/
theorem global_word_of_convolution_estimates {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    {α : ℝ} (K : (Fin n → ℝ) → ℝ) (hK : PositiveType G α K)
    (ν : HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    {ρ : ℝ} (hρ : 0 < ρ) (I : List (Fin (q+1)))
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate p r]
    (f : ℕ → (Fin n → ℝ) → ℝ) (F : (Fin n → ℝ) → ℝ)
    (hF : MemLp F p volume)
    (hfs : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) (hfc : ∀ j, HasCompactSupport (f j))
    (hsF : ∀ᵐ y ∂volume, ρ ≤ ν y → F y = 0)
    (hsf : ∀ j, ∀ᵐ y ∂volume, ρ ≤ ν y → f j y = 0)
    (hft : Tendsto (fun j => eLpNorm (f j-F) p volume) atTop (𝓝 0))
    (C : ℝ) (hC : 0 ≤ C)
    (hdiff : ∀ j l, eLpNorm
      (wordDerivative H.fields I (groupConvolution G (f j) K)-
        wordDerivative H.fields I (groupConvolution G (f l) K)) p volume ≤
          ENNReal.ofReal C*eLpNorm (f j-f l) p volume)
    (hbound : ∀ j, eLpNorm (wordDerivative H.fields I (groupConvolution G (f j) K)) p volume ≤
      ENNReal.ofReal C*eLpNorm (f j) p volume) :
    ∃ g : (Fin n → ℝ) → ℝ,
      hasWeakWordDeriv H.fields ⊤ I (groupConvolution G F K) g ∧
      MemLp g p volume ∧ eLpNorm g p volume ≤ ENNReal.ofReal C*eLpNorm F p volume := by
  have hf : ∀ j, MemLp (f j) p volume :=
    fun j => (hfs j).continuous.memLp_of_hasCompactSupport (hfc j)
  have hv : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (groupConvolution G (f j) K) :=
    fun j => contDiff_groupConvolution_left G (hfs j) (hfc j) (hK.locallyIntegrable ν.gauge)
  have hu := hK.locallyIntegrable_convolution ν h1 hsym hρ Fact.out hF hsF
  have hj : ∀ j, MemLp (wordDerivative H.fields I (groupConvolution G (f j) K)) p volume := by
    intro j
    exact lt_of_le_of_lt (hbound j) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hf j).eLpNorm_lt_top)
  have hjtop : ∀ j, MemLp (wordDerivative H.fields I (groupConvolution G (f j) K)) p
      (volume.restrict (⊤ : Opens (Fin n → ℝ))) := by simpa using hj
  have hsource := ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf F hF).mpr hft).cauchySeq
  have hc := lp_cauchy_of_difference_estimate volume
    (volume.restrict (⊤ : Opens (Fin n → ℝ))) p f
    (fun j => wordDerivative H.fields I (groupConvolution G (f j) K)) hf hjtop C hC hsource
    (fun j l => by simpa using hdiff j l)
  have hlocal := fun (U : Opens (Fin n → ℝ))
    (hU : IsCompact (closure (U : Set (Fin n → ℝ)))) =>
      hK.convolution_tendsto_relCompact ν h1 hsym hρ Fact.out f hF hf hsF hsf hft U hU
  obtain ⟨g,hg,hgl,hgt⟩ := weak_word_of_global_cauchy_jets_and_local_input
    (⊤ : Opens (Fin n → ℝ)) H.fields (fun i => (H.fields_smooth G i).contDiffOn) I p r
    (fun j => groupConvolution G (f j) K) (groupConvolution G F K)
    (fun j => (hv j).contDiffOn) (hu.locallyIntegrableOn _)
    (fun U hU _ => (hlocal U hU).2.1) (fun U hU _ => (hlocal U hU).1)
    (fun U hU _ => (hlocal U hU).2.2) hjtop hc
  have hglv : MemLp g p volume := by simpa using hgl
  have hgtv : Tendsto (fun j => eLpNorm
      (wordDerivative H.fields I (groupConvolution G (f j) K)-g) p volume) atTop (𝓝 0) := by
    simpa using hgt
  exact ⟨g,hg,hglv,lp_estimate_of_approximation volume Fact.out hF hglv hf hj
    hft hgtv C hbound⟩

end RothschildStein.H3

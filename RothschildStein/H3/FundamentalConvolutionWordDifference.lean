-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FundamentalConvolutionDifference
public import RothschildStein.H3.SmoothFundamentalPotentialJets

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H3

/-- Every classical word jet of a difference of smooth
compact-source fundamental potentials equals the jet of the actual
source difference pointwise. Shared weak linearity supplies the
almost-everywhere identity; continuity upgrades it for Hölder norms. -/
theorem fundamental_convolution_word_sub {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (I : List (Fin (q + 1))) (f g : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsf : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hsg : HasCompactSupport g) :
    wordDerivative H.fields I (G2.groupConvolution G f K) -
      wordDerivative H.fields I (G2.groupConvolution G g K) =
      wordDerivative H.fields I (G2.groupConvolution G (f - g) K) := by
  have hcf := ((smooth_fundamental_potential_jets G H K hQ f hf hsf).2.2.1 I).2.2
  have hcg := ((smooth_fundamental_potential_jets G H K hQ g hg hsg).2.2.1 I).2.2
  have hcd := ((smooth_fundamental_potential_jets G H K hQ (f - g)
    (hf.sub hg) (hsf.sub hsg)).2.2.1 I).2.2
  have hae : (wordDerivative H.fields I (G2.groupConvolution G f K) -
      wordDerivative H.fields I (G2.groupConvolution G g K)) =ᵐ[
        volume.restrict (univ : Set (Fin N → ℝ))]
      wordDerivative H.fields I (G2.groupConvolution G (f - g) K) := by
    simpa only [Measure.restrict_univ] using
      fundamental_convolution_word_sub_ae G H K I f g hf hsf hg hsg
  have he := Measure.eqOn_open_of_ae_eq hae isOpen_univ
    (hcf.sub hcg).continuous.continuousOn hcd.continuous.continuousOn
  exact funext (fun x => he (mem_univ x))

end RothschildStein.H3

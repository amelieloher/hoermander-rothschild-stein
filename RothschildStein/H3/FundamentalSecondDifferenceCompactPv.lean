-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FundamentalSecondBoundCompactPv
public import RothschildStein.H3.FundamentalConvolutionDifference

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal

/-- one positive constant controls the complete second jets
and their source differences. The Cauchy estimate is derived from actual
potential linearity, rather than an additional analytic premise. -/
theorem fundamental_second_and_difference_bounds_of_compact_principalValue_bounds {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (M : ℝ) (hM : 0 ≤ M)
    (hLp : ∀ i j : Fin q, ∀ f : (Fin n → ℝ) → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm (H1.principalValueConvolution G H.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) f) p volume ≤
          ENNReal.ofReal M*eLpNorm f p volume) :
    ∃ C₉ : ℝ, 0 < C₉ ∧
      (∀ f : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
          eLpNorm (wordDerivative H.fields I (G2.groupConvolution G f K)) p volume ≤
            ENNReal.ofReal C₉*eLpNorm f p volume) ∧
      ∀ f g : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
          eLpNorm (wordDerivative H.fields I (G2.groupConvolution G f K)-
            wordDerivative H.fields I (G2.groupConvolution G g K)) p volume ≤
              ENNReal.ofReal C₉*eLpNorm (f-g) p volume := by
  obtain ⟨C₉,hC₉,hbound⟩ := fundamental_second_bound_of_compact_principalValue_bounds G H K hQ p hp M hM hLp
  refine ⟨C₉,hC₉,hbound,?_⟩
  intro f g hf hsf hg hsg I hI
  rw [eLpNorm_congr_ae (fundamental_convolution_word_sub_ae G H K I f g hf hsf hg hsg)]
  exact hbound (f-g) (hf.sub hg) (hsf.sub hsg) I hI

end RothschildStein.H3

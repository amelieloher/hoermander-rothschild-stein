-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.KernelPotential
public import RothschildStein.S.WeakSub
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace

/-- the actual fundamental potential is linear under differences
of compact smooth sources. Absolute convergence justifies subtraction. -/
theorem fundamental_convolution_sub {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H)
    (f g : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsf : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hsg : HasCompactSupport g) :
    G2.groupConvolution G (f-g) K = G2.groupConvolution G f K-G2.groupConvolution G g K := by
  funext x
  simp only [G2.groupConvolution_eq_integral, Pi.sub_apply, sub_mul]
  apply integral_sub
  · simpa only [mul_comm] using
      H1.integrable_fundamentalPotential_second G K.locallyIntegrable hf.continuous hsf x
  · simpa only [mul_comm] using
      H1.integrable_fundamentalPotential_second G K.locallyIntegrable hg.continuous hsg x

/-- all classical jets of potential differences agree almost
everywhere with the potential of the source difference. Weak uniqueness
supplies linearity without a separate differential-operator premise. -/
theorem fundamental_convolution_word_sub_ae {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (I : List (Fin (q+1)))
    (f g : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsf : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hsg : HasCompactSupport g) :
    wordDerivative H.fields I (G2.groupConvolution G f K)-
      wordDerivative H.fields I (G2.groupConvolution G g K) =ᵐ[volume]
        wordDerivative H.fields I (G2.groupConvolution G (f-g) K) := by
  let φ : TestFunction (⊤ : Opens (Fin n → ℝ)) ℝ (⊤ : ℕ∞) := ⟨f,hf,hsf,subset_univ _⟩
  let ψ : TestFunction (⊤ : Opens (Fin n → ℝ)) ℝ (⊤ : ℕ∞) := ⟨g,hg,hsg,subset_univ _⟩
  have hcf : G2.groupConvolution G f K = G.potential K φ := by
    funext x
    rw [G2.groupConvolution_eq_integral]
    rfl
  have hcg : G2.groupConvolution G g K = G.potential K ψ := by
    funext x
    rw [G2.groupConvolution_eq_integral]
    rfl
  have hvf : ContDiff ℝ (⊤ : ℕ∞) (G2.groupConvolution G f K) := by rw [hcf]; exact K.potential_smooth φ
  have hvg : ContDiff ℝ (⊤ : ℕ∞) (G2.groupConvolution G g K) := by rw [hcg]; exact K.potential_smooth ψ
  have hX := fun i => (H.fields_smooth G i).contDiffOn (s := (univ : Set (Fin n → ℝ)))
  have hdf := S.hasWeakWordDeriv_classical ⊤ H.fields hX I _ hvf.contDiffOn
  have hdg := S.hasWeakWordDeriv_classical ⊤ H.fields hX I _ hvg.contDiffOn
  have hdiff := S.hasWeakWordDeriv_sub H.fields ⊤ hX hdf hdg
  have hclass := S.hasWeakWordDeriv_classical ⊤ H.fields hX I _ (hvf.sub hvg).contDiffOn
  have he := S.hasWeakWordDeriv_unique H.fields ⊤ hdiff hclass
  change (wordDerivative H.fields I (G2.groupConvolution G f K)-
    wordDerivative H.fields I (G2.groupConvolution G g K)) =ᵐ[volume.restrict (univ : Set (Fin n → ℝ))]
      wordDerivative H.fields I (G2.groupConvolution G f K-G2.groupConvolution G g K) at he
  rw [← fundamental_convolution_sub G H K f g hf hsf hg hsg] at he
  simpa only [Opens.coe_top, Measure.restrict_univ] using he

end RothschildStein.H3

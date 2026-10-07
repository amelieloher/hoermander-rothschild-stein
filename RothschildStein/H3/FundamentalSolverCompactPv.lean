-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FundamentalLocalWordBoundsCompactPv
public import RothschildStein.H3.FundamentalSecondDifferenceCompactPv
public import RothschildStein.H3.FundamentalJetConditional
public import RothschildStein.H3.LocalSobolevConvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

/-- The fundamental kernel solves each compact-source Lp problem for a
smoothly approximable source under the principal-value Lp bounds. The theorem
provides local and global jet estimates, Cauchy bounds, and approximation
equations with constants uniform in the source and approximation sequence. -/
theorem fundamental_solver_of_compact_principalValue_bounds {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (ρ : ℝ) (hρ : 0 < ρ)
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate p r]
    (M : ℝ) (hM : 0 ≤ M)
    (hLp : ∀ i j : Fin q, ∀ F : (Fin n → ℝ) → ℝ, ContDiff ℝ 1 F → HasCompactSupport F →
      eLpNorm (H1.principalValueConvolution G H.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) F) p volume ≤
          ENNReal.ofReal M*eLpNorm F p volume) :
    ∃ (C : ℝ → List (Fin (q+1)) → ℝ) (C₉ : ℝ), 0 < C₉ ∧
      (∀ R : ℝ, 0 < R → ∀ I ∈ wordFamily driftWeight 2, 0 < C R I) ∧
      ∀ (f : ℕ → (Fin n → ℝ) → ℝ) (F : (Fin n → ℝ) → ℝ),
        MemLp F p volume →
        (∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) → (∀ j, HasCompactSupport (f j)) →
        (∀ᵐ y ∂volume, ρ ≤ ν y → F y = 0) →
        (∀ j, ∀ᵐ y ∂volume, ρ ≤ ν y → f j y = 0) →
        Tendsto (fun j => eLpNorm (f j-F) p volume) atTop (𝓝 0) →
        ConvolutionLocalSolutions G H ν p F K C ∧
        memSobolevXLoc driftWeight H.fields ⊤ 2 p (G2.groupConvolution G F K) ∧
        driftSecondWeakENorm H.fields ⊤ p (G2.groupConvolution G F K) ≤
          (driftSecondWordFamily q).card*ENNReal.ofReal C₉*eLpNorm F p volume := by
  obtain ⟨B,hB⟩ := fundamental_local_word_bounds_of_compact_principalValue_bounds
    G H K hQ ν h1 hsym ρ hρ p Fact.out M hM hLp
  obtain ⟨C₉,hC₉,hglobal,hdifference⟩ := fundamental_second_and_difference_bounds_of_compact_principalValue_bounds
    G H K hQ p Fact.out M hM hLp
  let C := fun R : ℝ => fun _ : List (Fin (q+1)) => B R
  refine ⟨C,C₉,hC₉,fun R hR _ _ => (hB R hR).1,?_⟩
  intro f F hF hfs hfc hsF hsf hft
  have hdiff : ∀ R : ℝ, 0 < R → ∀ I ∈ wordFamily driftWeight 2, ∀ j l,
      eLpNorm (wordDerivative H.fields I (G2.groupConvolution G (f j) K)-
        wordDerivative H.fields I (G2.groupConvolution G (f l) K)) p
        (volume.restrict (quasiballDomain G ν 0 R : Set (Fin n → ℝ))) ≤
          ENNReal.ofReal (C R I)*eLpNorm (f j-f l) p volume := by
    intro R hR I hI j l
    have he : (wordDerivative H.fields I (G2.groupConvolution G (f j) K)-
        wordDerivative H.fields I (G2.groupConvolution G (f l) K)) =ᵐ[volume.restrict
          (quasiballDomain G ν 0 R : Set (Fin n → ℝ))]
        wordDerivative H.fields I (G2.groupConvolution G (f j-f l) K) :=
      (fundamental_convolution_word_sub_ae G H K I (f j) (f l)
      (hfs j) (hfc j) (hfs l) (hfc l)).filter_mono (ae_mono Measure.restrict_le_self)
    rw [eLpNorm_congr_ae he]
    apply (hB R hR).2 (f j-f l) ((hfs j).sub (hfs l)) ((hfc j).sub (hfc l)) _ I hI
    filter_upwards [hsf j,hsf l] with y hy hz
    intro h
    simp only [Pi.sub_apply,hy h,hz h,sub_self]
  have hresult := convolution_local_and_global_of_fundamental_jet_estimates G H K ν h1 hsym hρ
    p r f F hF hfs hfc hsF hsf hft C
    (fun R hR I hI => ((hB R hR).1).le) hdiff
    (fun R hR I hI j => (hB R hR).2 (f j) (hfs j) (hfc j) (hsf j) I hI)
    C₉ hC₉.le
    (fun I hI j l => hdifference (f j) (f l) (hfs j) (hfc j) (hfs l) (hfc l) I hI)
    (fun I hI j => hglobal (f j) (hfs j) (hfc j) I hI)
  exact ⟨hresult.1,convolution_memSobolevXLoc_of_solutions G H ν p F K C hresult.1,hresult.2⟩

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ConvolutionFormulas
public import RothschildStein.S.ClassicalWords
public import RothschildStein.S.WeakIntrinsicWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators
namespace RothschildStein.H3

/-- A smooth compact source has an actual smooth fundamental
potential with normalized weak and intrinsic jets of every word.
Its drift-plus-diagonal source is exactly the original source.
No compact support condition is imposed on the potential or its jets. -/
theorem smooth_fundamental_potential_jets {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ) :
    let v := G2.groupConvolution G φ K
    let jet := fun I => wordDerivative H.fields I v
    ContDiff ℝ (⊤ : ℕ∞) v ∧ jet [] = v ∧
      (∀ I : List (Fin (q + 1)), hasWeakWordDeriv H.fields ⊤ I v (jet I) ∧
        hasIntrinsicWordDeriv H.fields ⊤ I v (jet I) ∧ ContDiff ℝ (⊤ : ℕ∞) (jet I)) ∧
      (fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x) = φ := by
  let v := G2.groupConvolution G φ K
  let jet := fun I => wordDerivative H.fields I v
  have hp := (Classical.choose_spec (convolution_formulas_of_fundamental_kernel G H K hQ)).2 φ hφ hsφ
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := hp.1
  have hc (I : List (Fin (q + 1))) : ContDiff ℝ (⊤ : ℕ∞) (jet I) :=
    contDiffOn_univ.mp (S.contDiffOn_wordDerivative ⊤ H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) I v hv.contDiffOn)
  have hw (I : List (Fin (q + 1))) : hasWeakWordDeriv H.fields ⊤ I v (jet I) :=
    S.hasWeakWordDeriv_classical ⊤ H.fields (fun i => (H.fields_smooth G i).contDiffOn)
      I v hv.contDiffOn
  refine ⟨hv, rfl, ?_, ?_⟩
  · intro I
    refine ⟨hw I, ?_, hc I⟩
    exact S.hasIntrinsicWordDeriv_of_continuous_weak_subwords ⊤ H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) I v jet rfl
      (fun J _ => hw J) (fun J _ => (hc J).continuous.continuousOn)
  · exact hp.2.1

end RothschildStein.H3

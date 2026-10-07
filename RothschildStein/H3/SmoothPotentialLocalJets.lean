-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SmoothFundamentalPotentialJets
public import RothschildStein.S.IntrinsicNormRepresentatives

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- The classical jets of an actual smooth compact-source
fundamental potential are intrinsic representatives on every open domain. -/
theorem smooth_fundamental_potential_intrinsic_on {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsφ : HasCompactSupport φ) (U : Opens (Fin N → ℝ))
    (I : List (Fin (q + 1))) :
    hasIntrinsicWordDeriv H.fields U I (G2.groupConvolution G φ K)
      (wordDerivative H.fields I (G2.groupConvolution G φ K)) := by
  let v := G2.groupConvolution G φ K
  have hv : ContDiff ℝ (⊤ : ℕ∞) v :=
    (smooth_fundamental_potential_jets G H K hQ φ hφ hsφ).1
  have hX (i : Fin (q + 1)) :=
    (H.fields_smooth G i).contDiffOn (s := (U : Set (Fin N → ℝ)))
  exact S.hasIntrinsicWordDeriv_of_continuous_weak_subwords U H.fields hX
    I v (fun J => wordDerivative H.fields J v) rfl
    (fun J _ => S.hasWeakWordDeriv_classical U H.fields hX J v hv.contDiffOn)
    (fun J _ => (S.contDiffOn_wordDerivative U H.fields hX J v hv.contDiffOn).continuousOn)

/-- Each classical word jet realizes the exact fixed infimum
norm of the fundamental potential on the chosen open domain. -/
theorem smooth_fundamental_potential_intrinsic_norm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsφ : HasCompactSupport φ) (U : Opens (Fin N → ℝ))
    (I : List (Fin (q + 1))) (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (α : ℝ) :
    intrinsicWordENorm H.fields d U I α (G2.groupConvolution G φ K) =
      holderENorm d α (U : Set (Fin N → ℝ))
        (wordDerivative H.fields I (G2.groupConvolution G φ K)) := by
  exact S.intrinsicWordENorm_eq_representative U H.fields d I α _ _
    (smooth_fundamental_potential_intrinsic_on G H K hQ φ hφ hsφ U I)

end RothschildStein.H3

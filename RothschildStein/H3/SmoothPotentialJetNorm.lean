-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SmoothPotentialLocalJets
public import RothschildStein.H3.FundamentalConvolutionWordDifference
public import RothschildStein.S.Sobolev
public import RothschildStein.Definitions.holderXENorm
public import RothschildStein.Definitions.driftWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- The full fixed norm of a smooth fundamental potential
is the finite sum of its actual classical jet norms. -/
theorem smooth_fundamental_potential_holderX_norm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsφ : HasCompactSupport φ) (U : Opens (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞) (k : ℕ) (α : ℝ) :
    holderXENorm driftWeight H.fields d U k α (G2.groupConvolution G φ K) =
      ∑ I ∈ wordFamily driftWeight k, holderENorm d α (U : Set (Fin N → ℝ))
        (wordDerivative H.fields I (G2.groupConvolution G φ K)) := by
  unfold holderXENorm
  apply Finset.sum_congr rfl
  intro I _
  exact smooth_fundamental_potential_intrinsic_norm G H K hQ φ hφ hsφ U I d α

/-- A full fixed potential bound controls each weighted jet,
with no change in its constant. -/
theorem smooth_fundamental_potential_jet_norm_le {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsφ : HasCompactSupport φ) (U : Opens (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞) (k : ℕ) (α : ℝ)
    (I : List (Fin (q + 1))) (hI : wordWeight (driftWeight (q := q)) I ≤ k) :
    holderENorm d α (U : Set (Fin N → ℝ))
        (wordDerivative H.fields I (G2.groupConvolution G φ K)) ≤
      holderXENorm driftWeight H.fields d U k α (G2.groupConvolution G φ K) := by
  rw [smooth_fundamental_potential_holderX_norm G H K hQ φ hφ hsφ U d k α]
  exact Finset.single_le_sum (f := fun J : List (Fin (q + 1)) =>
    holderENorm d α (U : Set (Fin N → ℝ))
      (wordDerivative H.fields J (G2.groupConvolution G φ K))) (fun _ _ => zero_le)
    ((S.mem_wordFamily_iff driftWeight k I).mpr hI)

end RothschildStein.H3

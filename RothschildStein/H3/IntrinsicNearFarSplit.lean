-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicJetSourceData
public import RothschildStein.H3.NearFarConvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace RothschildStein.H3

/-- The actual intrinsic source splits into its near convolution
and the right-operator far convolution of the original input. All
integrability and mollification hypotheses are discharged from compact
continuous intrinsic order-two jets. -/
theorem intrinsic_source_near_far_split {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (μ : G2.GroupMollifier G H.norm) (u : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) (hzero : jet [] = u)
    (hi : ∀ I, wordWeight driftWeight I ≤ 2 → hasIntrinsicWordDeriv H.fields ⊤ I u (jet I))
    (hc : ∀ I, wordWeight driftWeight I ≤ 2 → Continuous (jet I))
    (hs : ∀ I, wordWeight driftWeight I ≤ 2 → HasCompactSupport (jet I))
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {T : (Fin N → ℝ) → ℝ} (hT : LocallyIntegrable T volume)
    (hsT : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ)
    {ε : ℝ} (hε : 0 < ε) (x : Fin N → ℝ) :
    let F := fun y => jet [0] y + ∑ i : Fin q, jet [i.succ, i.succ] y
    G2.groupConvolution G F T x =
      G2.groupConvolution G F
        (fun w => smoothQuasiballCutoff G ν 0 (ε / 2) ε w * T w) x +
      G2.groupConvolution G u
        (sumSquaresWithDrift (fun i => G2.rightField G (H.fields i 0))
          (exteriorCutoffKernel ν interpolationCutoffProfile T ε)) x := by
  have hdata := intrinsicJetSource_data jet hc hs (A := univ) (fun _ _ => subset_univ _)
  have hE : ContDiff ℝ (⊤ : ℕ∞) (exteriorCutoffKernel ν interpolationCutoffProfile T ε) :=
    contDiff_kernel_exterior_cutoff ν.gauge hν interpolationCutoffProfile_smooth
      (fun _ ht => interpolationCutoffProfile_one ht) hsT hε
  have hsplit := groupConvolution_near_far_split G ν hν hdata.1 hdata.2.1 hT hsT hε x
  have hfar := intrinsic_sumSquares_convolution_transfer G H μ u jet hzero hi hc hs hE x
  rw [hfar] at hsplit
  exact hsplit

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.InterpolationCutoffProfile
public import RothschildStein.H3.ExteriorKernelScaling
public import RothschildStein.H3.FarKernelTransfer
public import RothschildStein.H1.LocallyIntegrablePotentialDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H3

/-- Exact near/far split with the common smooth radial profile.
Absolute convergence of the near part follows by subtracting the smooth
exterior kernel from the locally integrable full kernel. -/
theorem groupConvolution_near_far_split {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (hsν : ν.Smooth)
    {u T : (Fin N → ℝ) → ℝ} (hu : Continuous u) (hsu : HasCompactSupport u)
    (hT : LocallyIntegrable T volume)
    (hsT : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ)
    {ε : ℝ} (hε : 0 < ε) (x : Fin N → ℝ) :
    G2.groupConvolution G u T x =
      G2.groupConvolution G u
        (fun w => smoothQuasiballCutoff G ν 0 (ε / 2) ε w * T w) x +
      G2.groupConvolution G u
        (exteriorCutoffKernel ν interpolationCutoffProfile T ε) x := by
  let E := exteriorCutoffKernel ν interpolationCutoffProfile T ε
  let A := fun w => smoothQuasiballCutoff G ν 0 (ε / 2) ε w * T w
  have he : ContDiff ℝ (⊤ : ℕ∞) E := contDiff_kernel_exterior_cutoff ν.gauge hsν
    interpolationCutoffProfile_smooth (fun _ ht => interpolationCutoffProfile_one ht) hsT hε
  have hi := H1.groupConvolutionExistsAt_of_localKernel G hT hu hsu x
  have hie := groupConvolution_exists_compact_continuous_kernel G hu hsu he.continuous x
  have hsplit : T = A + E := by
    funext w
    change T w = smoothQuasiballCutoff G ν 0 (ε / 2) ε w * T w +
      (1 - interpolationCutoffProfile (ν w / ε)) * T w
    rw [near_cutoff_eq_interpolation_profile G ν hε]
    ring
  have hia : G2.GroupConvolutionExistsAt G u A x := by
    have hh := hi.sub hie
    change Integrable (fun y => u y * A (G.mul (G.inv y) x)) volume
    have heq : (fun y => u y * A (G.mul (G.inv y) x)) =
        ((fun y => u y * T (G.mul (G.inv y) x)) -
          (fun y => u y * E (G.mul (G.inv y) x))) := by
      funext y
      simp only [Pi.sub_apply]
      have hp := congrFun hsplit (G.mul (G.inv y) x)
      simp only [Pi.add_apply] at hp
      rw [hp]
      ring
    rw [heq]
    exact hh
  change G2.groupConvolution G u T x =
    G2.groupConvolution G u A x + G2.groupConvolution G u E x
  rw [hsplit]
  exact G2.groupConvolution_add_right G u A E x hia hie

end RothschildStein.H3

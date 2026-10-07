-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.KernelData
public import RothschildStein.H1.PotentialDerivative
public import RothschildStein.H1.StandingKernelCancellation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N) (H : StandingHypotheses G q)

/-- The first horizontal derivative of a compact smooth
function is the actual potential of YⱼΓ against Lu, with drift retained. -/
theorem FundamentalKernel.firstDerivative_representation (K : FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) (j : Fin q)
    {u : (Fin N → ℝ) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hsu : HasCompactSupport u) :
    fieldDerivative (H.fields j.succ) u =
      G2.groupConvolution G (sumSquaresWithDrift H.fields u) (fieldDerivative (H.fields j.succ) K) := by
  let ut : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) := ⟨u, hu, hsu, subset_univ _⟩
  let ψ := sumSquaresTest ⊤ H.fields (fun i => (H.fields_smooth G i).contDiffOn) ut
  have heψ : (ψ : (Fin N → ℝ) → ℝ) = sumSquaresWithDrift H.fields u :=
    funext fun x => sumSquaresTest_apply ⊤ H.fields (fun i => (H.fields_smooth G i).contDiffOn) ut x
  have he : G2.groupConvolution G (sumSquaresWithDrift H.fields u) K = u := by
    funext x
    rw [G2.groupConvolution_eq_integral]
    have ht := H.fundamental_twoSidedInverse G hQ K.locallyIntegrable K.smooth_off_zero K.homogeneous K.fundamental hu hsu x
    convert ht using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun _ => mul_comm _ _
  have hd := H.fieldDerivative_homogeneousPotential G j
    (K.smooth_off_zero.of_le (by simp)) K.homogeneous (by linarith)
    ψ.contDiff ψ.hasCompactSupport
  rw [heψ, he] at hd
  exact hd

/-- The first differentiated kernel integrand is
absolutely integrable at every point. -/
theorem FundamentalKernel.firstDerivative_integrable (K : FundamentalKernel G H)
    (j : Fin q) {u : (Fin N → ℝ) → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hsu : HasCompactSupport u) (x : Fin N → ℝ) :
    Integrable (fun y => sumSquaresWithDrift H.fields u y *
      fieldDerivative (H.fields j.succ) K (G.mul (G.inv y) x)) volume := by
  let ut : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) := ⟨u, hu, hsu, subset_univ _⟩
  let ψ := sumSquaresTest ⊤ H.fields (fun i => (H.fields_smooth G i).contDiffOn) ut
  have heψ : (ψ : (Fin N → ℝ) → ℝ) = sumSquaresWithDrift H.fields u :=
    funext fun y => sumSquaresTest_apply ⊤ H.fields (fun i => (H.fields_smooth G i).contDiffOn) ut y
  have hiK := H.horizontalKernel_locallyIntegrable G j
    (K.smooth_off_zero.of_le (by simp)) K.homogeneous (by linarith)
  have hi := groupConvolutionExistsAt_of_localKernel G hiK ψ.contDiff.continuous ψ.hasCompactSupport x
  change Integrable (fun y => ψ y * fieldDerivative (H.fields j.succ) K (G.mul (G.inv y) x)) volume at hi
  rw [heψ] at hi
  exact hi

end RothschildStein.H1

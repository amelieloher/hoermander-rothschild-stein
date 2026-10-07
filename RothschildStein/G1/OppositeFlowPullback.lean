-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.FlowPullback
public import RothschildStein.G1.FlowJacobianInverse
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

/-- The opposite-time Jacobian is the ring inverse of the forward
Jacobian wherever both local branches exist (BB Lemma 1.52, pp. 30–31). -/
theorem localFlow_opposite_fderiv_eq_ringInverse_of_joint_contDiff
    {N : ℕ} {Ω U : Set (Fin N → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {Z : (Fin N → ℝ) → (Fin N → ℝ)} (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω)
    {τ : ℝ} (hτ : 0 < τ) (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hend : Φ (x, t) ∈ U) :
    fderiv ℝ (fun y => Φ (y, -t)) (Φ (x, t)) =
      Ring.inverse (fderiv ℝ (fun y => Φ (y, t)) x) := by
  let J := fderiv ℝ (fun y => Φ (y, t)) x
  have hdet := localFlow_jacobian_ne_zero_of_joint_contDiff hΩ hU hZ hτ Φ hjoint hΦ hx ht hend
  let L := J.toContinuousLinearEquivOfDetNeZero hdet
  have hL : (L : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) = J :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero J hdet
  have hunit : IsUnit J := ⟨L.toUnit, hL⟩
  have hprod := localFlow_inverse_fderiv_of_joint_contDiff hΩ hU hZ hτ Φ hjoint hΦ hx ht hend
  change (fderiv ℝ (fun y => Φ (y, -t)) (Φ (x, t))) * J = 1 at hprod
  simpa only [one_mul] using (Ring.eq_mul_inverse_iff_mul_eq _ 1 J hunit).mpr hprod

end RothschildStein.G1

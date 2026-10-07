-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.OppositeFlowPullback
public import RothschildStein.G1.FlowVariational
public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G4

/-- The inverse of a fundamental matrix solving J′=D·J solves
A′=−A·D at every invertible point (BB Lemma 9.48, pp. 441–442). -/
theorem inverse_fundamental_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (J : ℝ → E →L[ℝ] E)
    (D : E →L[ℝ] E) (s : ℝ) (hunit : IsUnit (J s))
    (hJ : HasDerivAt J (D.comp (J s)) s) :
    HasDerivAt (fun v => Ring.inverse (J v)) (-(Ring.inverse (J s)).comp D) s := by
  obtain ⟨u, hu⟩ := hunit
  have hui : ((u⁻¹ : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) = Ring.inverse (J s) := by
    rw [← hu, Ring.inverse_unit]
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu, hui] at hi
  have hh := hi.comp_hasDerivAt s hJ
  have hcancel := Ring.mul_inverse_cancel (J s) (show IsUnit (J s) from ⟨u, hu⟩)
  change J s * Ring.inverse (J s) = 1 at hcancel
  simpa only [Function.comp_def, neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    ← ContinuousLinearMap.mul_def, mul_assoc, hcancel, mul_one] using hh

/-- The actual opposite-time flow Jacobian solves the inverse
fundamental-matrix equation on the finite local trajectory overlap.
No invariant flow domain is presumed (BB Lemma 9.48, pp. 441–442). -/
theorem localFlow_opposite_jacobian_hasDerivAt_of_joint_contDiff
    {N : ℕ} {Ω U : Set (Fin N → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {Z : (Fin N → ℝ) → (Fin N → ℝ)} (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω)
    {τ : ℝ} (hτ : 0 < τ) (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) {s : ℝ} (hs : s ∈ Ioo (-τ) τ)
    (hend : Φ (x, s) ∈ U) :
    HasDerivAt (fun v => fderiv ℝ (fun y => Φ (y, -v)) (Φ (x, v)))
      (-(fderiv ℝ (fun y => Φ (y, -s)) (Φ (x, s))).comp (fderiv ℝ Z (Φ (x, s)))) s := by
  let J : ℝ → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := fun v => fderiv ℝ (fun y => Φ (y, v)) x
  have hdet := RothschildStein.G1.localFlow_jacobian_ne_zero_of_joint_contDiff
    hΩ hU hZ hτ Φ hjoint hΦ hx hs hend
  let L := (J s).toContinuousLinearEquivOfDetNeZero hdet
  have hL : (L : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) = J s :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero (J s) hdet
  have hunit : IsUnit (J s) := ⟨L.toUnit, hL⟩
  have hJ := RothschildStein.G1.localFlow_variational_of_joint_contDiff hΩ hU hZ Φ hjoint
    (fun y hy => (hΦ y hy).2) hx hs
  have hi := inverse_fundamental_hasDerivAt J (fderiv ℝ Z (Φ (x, s))) s hunit hJ
  have hα := ((hΦ x hx).2 s hs).1.continuousAt
  have heq : (fun v => fderiv ℝ (fun y => Φ (y, -v)) (Φ (x, v))) =ᶠ[𝓝 s]
      (fun v => Ring.inverse (J v)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs, hα.eventually_mem (hU.mem_nhds hend)] with v hv he
    exact RothschildStein.G1.localFlow_opposite_fderiv_eq_ringInverse_of_joint_contDiff
      hΩ hU hZ hτ Φ hjoint hΦ hx hv he
  rw [← RothschildStein.G1.localFlow_opposite_fderiv_eq_ringInverse_of_joint_contDiff
    hΩ hU hZ hτ Φ hjoint hΦ hx hs hend] at hi
  exact hi.congr_of_eventuallyEq heq

end RothschildStein.G4

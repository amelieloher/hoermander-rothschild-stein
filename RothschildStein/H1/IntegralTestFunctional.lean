-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakDeriv
public import Mathlib.Analysis.Distribution.Distribution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.H1
variable {N : ℕ} (Ω : Opens (Fin N → ℝ))

/-- The integrable representative defines a linear functional
on the actual compact test space (BB pp. 251–253). -/
def integralTestLinear (γ : (Fin N → ℝ) → ℝ) (hγ : Integrable γ) :
    TestFunction Ω ℝ (⊤ : ℕ∞) →ₗ[ℝ] ℝ where
  toFun φ := ∫ x, γ x * φ x
  map_add' φ ψ := by
    have hiφ : Integrable (fun x => γ x * φ x) :=
      hγ.locallyIntegrable.integrable_smul_right_of_hasCompactSupport φ.contDiff.continuous φ.hasCompactSupport
    have hiψ : Integrable (fun x => γ x * ψ x) :=
      hγ.locallyIntegrable.integrable_smul_right_of_hasCompactSupport ψ.contDiff.continuous ψ.hasCompactSupport
    change (∫ x, γ x * (φ + ψ) x) = _
    have he : (fun x => γ x * (φ + ψ) x) = fun x => γ x * φ x + γ x * ψ x := by
      funext x
      change γ x * (φ x + ψ x) = _
      ring
    rw [he, integral_add hiφ hiψ]
  map_smul' c φ := by
    change (∫ x, γ x * (c • φ) x) = c * ∫ x, γ x * φ x
    have he : (fun x => γ x * (c • φ) x) = fun x => c * (γ x * φ x) := by
      funext x
      change γ x * (c * φ x) = _
      ring
    rw [he, integral_const_mul]

/-- The L1 representative is an order-zero functional, with
its full integral norm as the coefficient (BB pp. 251–253). -/
theorem abs_integralTestLinear_le
    (γ : (Fin N → ℝ) → ℝ) (hγ : Integrable γ)
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    |integralTestLinear Ω γ hγ φ| ≤
      (∫ x, ‖γ x‖) * ‖(TestFunction.toBoundedContinuousFunctionCLM ℝ) φ‖ := by
  let M := ‖(TestFunction.toBoundedContinuousFunctionCLM ℝ) φ‖
  have hi : Integrable (fun x => γ x * φ x) :=
    hγ.locallyIntegrable.integrable_smul_right_of_hasCompactSupport φ.contDiff.continuous φ.hasCompactSupport
  have hb (x : Fin N → ℝ) : ‖φ x‖ ≤ M := by
    exact ((TestFunction.toBoundedContinuousFunctionCLM ℝ) φ).norm_coe_le_norm x
  change |∫ x, γ x * φ x| ≤ (∫ x, ‖γ x‖) * M
  calc
    _ ≤ ∫ x, ‖γ x * φ x‖ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => γ x * φ x)
    _ ≤ ∫ x, ‖γ x‖ * M := integral_mono hi.norm (hγ.norm.mul_const M)
      (fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _))
    _ = _ := integral_mul_const M (fun x => ‖γ x‖)

end RothschildStein.H1

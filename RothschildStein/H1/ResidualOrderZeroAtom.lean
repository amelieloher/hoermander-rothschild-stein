-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.IntegralTestFunctional
public import RothschildStein.H1.PointSupportedOrderZero

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.H1
variable {N : ℕ} (Ω : Opens (Fin N → ℝ))

/-- Subtracting the integrable representative leaves an
order-zero functional supported at zero, hence exactly a point mass.
The representation identity is required on every test away from zero
(BB pp. 251–253; order-zero route). -/
theorem orderZero_representation_residual_atom
    (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (T : TestFunction Ω ℝ (⊤ : ℕ∞) →ₗ[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ, |T φ| ≤ C * ‖(TestFunction.toBoundedContinuousFunctionCLM ℝ) φ‖)
    {γ : (Fin N → ℝ) → ℝ} (hγ : Integrable γ)
    (hrep : ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
      (0 : Fin N → ℝ) ∉ tsupport (φ : (Fin N → ℝ) → ℝ) → T φ = ∫ x, γ x * φ x) :
    ∃ α : ℝ, ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞), T φ = (∫ x, γ x * φ x) + α * φ 0 := by
  let R := T - integralTestLinear Ω γ hγ
  have hR : ∀ φ, |R φ| ≤ (C + ∫ x, ‖γ x‖) *
      ‖(TestFunction.toBoundedContinuousFunctionCLM ℝ) φ‖ := by
    intro φ
    change |T φ - integralTestLinear Ω γ hγ φ| ≤ _
    calc
      _ ≤ |T φ| + |integralTestLinear Ω γ hγ φ| := abs_sub _ _
      _ ≤ C * ‖(TestFunction.toBoundedContinuousFunctionCLM ℝ) φ‖ +
          (∫ x, ‖γ x‖) * ‖(TestFunction.toBoundedContinuousFunctionCLM ℝ) φ‖ :=
        add_le_add (hbound φ) (abs_integralTestLinear_le Ω γ hγ φ)
      _ = _ := by ring
  have haway : ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
      (0 : Fin N → ℝ) ∉ tsupport (φ : (Fin N → ℝ) → ℝ) → R φ = 0 := by
    intro φ hφ
    change T φ - (∫ x, γ x * φ x) = 0
    rw [hrep φ hφ, sub_self]
  obtain ⟨α, he⟩ := pointSupported_orderZero_eq_eval Ω h0 R
    (add_nonneg hC (integral_nonneg (fun x => norm_nonneg (γ x)))) hR haway
  refine ⟨α, ?_⟩
  intro φ
  have h := he φ
  change T φ - (∫ x, γ x * φ x) = α * φ 0 at h
  linarith

end RothschildStein.H1

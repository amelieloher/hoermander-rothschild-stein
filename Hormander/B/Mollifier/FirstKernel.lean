-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Mollifier.SymbolBounds
public import Hormander.B.Mollifier.Uniform

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace Hormander.B

variable {N : ℕ}

/-- The operator `M_a ∘ ∂_i`. -/
def DOp (a : TestFunction N) (i : Fin N) : Operator N :=
  (multiplierOperator a).comp (coordinateDerivative i)

/-- The Fourier symbol `2πi ξ_i` of `∂_i`. -/
def derivSym (i : Fin N) (x : Carrier N) : ℂ := 2 * Real.pi * Complex.I * coordC i x

theorem norm_derivSym (i : Fin N) (x : Carrier N) : ‖derivSym i x‖ ≤ 2 * Real.pi * ‖x‖ := by
  unfold derivSym
  rw [norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact mul_le_mul_of_nonneg_left (norm_coordC_le i x) (by positivity)

theorem continuous_derivSym (i : Fin N) : Continuous (derivSym i) := by
  unfold derivSym coordC
  fun_prop

theorem continuous_mollSymbol (δ : ℝ) (hδ : 0 < δ) : Continuous (mollSymbol N δ hδ) :=
  (𝓕 (Hormander.A.Jδ N δ hδ)).continuous

theorem fourier_DOp (a w : TestFunction N) (i : Fin N) (ξ : Carrier N) :
    𝓕 (DOp a i w) ξ = ∫ α, 𝓕 a α * (derivSym i (ξ - α) * 𝓕 w (ξ - α)) := by
  unfold DOp
  rw [LinearMap.comp_apply, fourier_mul_apply]
  congr 1; funext α
  rw [fourier_coordinateDerivative]
  rfl

theorem integrable_DOp_integrand (a w : TestFunction N) (i : Fin N) (ξ : Carrier N) :
    Integrable (fun α : Carrier N => 𝓕 a α * (derivSym i (ξ - α) * 𝓕 w (ξ - α))) := by
  have h := integrable_conv (𝓕 a) ((2 * Real.pi * Complex.I) • coordMul i (𝓕 w)) ξ
  refine h.congr (Filter.Eventually.of_forall fun α => ?_)
  simp only [smul_apply, coordMul_apply, smul_eq_mul, derivSym]
  ring

/-- Fourier transform of the first mollifier commutator. -/
theorem fourier_comm_moll_DOp (δ : ℝ) (hδ : 0 < δ) (a u : TestFunction N) (i : Fin N)
    (ξ : Carrier N) :
    𝓕 (operatorComm (mollOp N δ hδ) (DOp a i) u) ξ =
      ∫ α, 𝓕 a α * (derivSym i (ξ - α) *
        ((mollSymbol N δ hδ ξ - mollSymbol N δ hδ (ξ - α)) * 𝓕 u (ξ - α))) := by
  have e : operatorComm (mollOp N δ hδ) (DOp a i) u =
      mollOp N δ hδ (DOp a i u) - DOp a i (mollOp N δ hδ u) := rfl
  rw [e, fourier_sub_testFunction, sub_apply, fourier_mollOp, fourier_DOp, fourier_DOp]
  have h1 := (integrable_DOp_integrand a u i ξ).const_mul (mollSymbol N δ hδ ξ)
  have h2 := integrable_DOp_integrand a (mollOp N δ hδ u) i ξ
  have : (fun α : Carrier N => 𝓕 a α * (derivSym i (ξ - α) *
        ((mollSymbol N δ hδ ξ - mollSymbol N δ hδ (ξ - α)) * 𝓕 u (ξ - α)))) =
      fun α => mollSymbol N δ hδ ξ * (𝓕 a α * (derivSym i (ξ - α) * 𝓕 u (ξ - α))) -
        𝓕 a α * (derivSym i (ξ - α) * 𝓕 (mollOp N δ hδ u) (ξ - α)) := by
    funext α
    rw [fourier_mollOp]
    ring
  rw [this, integral_sub h1 h2, integral_const_mul]

end Hormander.B

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Fractional.Commutators

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace Hormander.B

variable {N : ℕ}

/-! Algebra of the commutator convention `[A,B] = A∘B − B∘A`. -/

theorem operatorComm_add_right (A B C : Operator N) :
    operatorComm A (B + C) = operatorComm A B + operatorComm A C := by
  ext u; simp [operatorComm]; try abel

theorem operatorComm_add_left (A B C : Operator N) :
    operatorComm (A + B) C = operatorComm A C + operatorComm B C := by
  ext u; simp [operatorComm]; try abel

theorem operatorComm_comp_right (A B C : Operator N) :
    operatorComm A (B.comp C) = (operatorComm A B).comp C + B.comp (operatorComm A C) := by
  ext u; simp [operatorComm]; try abel

theorem operatorComm_comp_left (A B C : Operator N) :
    operatorComm (A.comp B) C = A.comp (operatorComm B C) + (operatorComm A C).comp B := by
  ext u; simp [operatorComm]; try abel

theorem operatorComm_antisymm (A B : Operator N) : operatorComm A B = (-1 : ℂ) • operatorComm B A := by
  ext u; simp [operatorComm]

theorem operatorComm_jacobi (D L P : Operator N) :
    operatorComm D (operatorComm L P) =
      operatorComm (operatorComm D L) P + operatorComm L (operatorComm D P) := by
  ext u; simp [operatorComm]; try abel

theorem operatorComm_eq_zero_of_comm {A B : Operator N} (h : A.comp B = B.comp A) :
    operatorComm A B = 0 := by
  ext u : 1
  simp only [operatorComm, LinearMap.sub_apply, LinearMap.zero_apply]
  rw [LinearMap.congr_fun h u, sub_self]

/-! Coordinate derivatives. -/

theorem fourier_coordinateDerivative (i : Fin N) (u : TestFunction N) (ξ : Carrier N) :
    𝓕 (coordinateDerivative i u) ξ = (2 * Real.pi * Complex.I * (ξ i : ℂ)) * 𝓕 u ξ := by
  have h := Hormander.A.fourier_schwartz_lineDeriv u (EuclideanSpace.single i (1 : ℝ))
  have e : coordinateDerivative i u =
      LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) u := rfl
  rw [e, h, smul_apply]
  have hg : (fun x : Carrier N => inner ℝ x (EuclideanSpace.single i (1 : ℝ))).HasTemperateGrowth := by
    fun_prop
  rw [SchwartzMap.smulLeftCLM_apply_apply hg]
  simp only [smul_eq_mul, EuclideanSpace.inner_single_right, one_mul, conj_trivial]
  simp only [Complex.real_smul]
  ring

theorem lambdaOperator_comp_coordinateDerivative (σ : ℝ) (i : Fin N) :
    (lambdaOperator σ).comp (coordinateDerivative i) =
      (coordinateDerivative i).comp (lambdaOperator σ) := by
  ext u : 1
  have hinj : Function.Injective (𝓕 : TestFunction N → TestFunction N) :=
    (Hormander.A.fourier_schwartz_bijective (N := N)).1
  apply hinj
  ext ξ
  simp only [LinearMap.comp_apply, fourier_lambdaOperator, fourier_coordinateDerivative]
  ring

theorem operatorComm_lambda_coordinateDerivative (σ : ℝ) (i : Fin N) :
    operatorComm (lambdaOperator σ) (coordinateDerivative i) = 0 :=
  operatorComm_eq_zero_of_comm (lambdaOperator_comp_coordinateDerivative σ i)

theorem coordinateDerivative_comp_comm (i j : Fin N) :
    (coordinateDerivative i).comp (coordinateDerivative j) =
      (coordinateDerivative j).comp (coordinateDerivative i) := by
  ext u : 1
  have hinj : Function.Injective (𝓕 : TestFunction N → TestFunction N) :=
    (Hormander.A.fourier_schwartz_bijective (N := N)).1
  apply hinj
  ext ξ
  simp only [LinearMap.comp_apply, fourier_coordinateDerivative]
  ring

theorem operatorComm_coordinateDerivative_coordinateDerivative (i j : Fin N) :
    operatorComm (coordinateDerivative i) (coordinateDerivative j) = 0 :=
  operatorComm_eq_zero_of_comm (coordinateDerivative_comp_comm i j)

/-- Leibniz rule: the commutator of a coordinate derivative with a multiplier is the multiplier
by the derivative of the coefficient. -/
theorem operatorComm_coordinateDerivative_multiplier (i : Fin N) (g : TestFunction N) :
    operatorComm (coordinateDerivative i) (multiplierOperator g) =
      multiplierOperator (coordinateDerivative i g) := by
  ext u x
  simp only [operatorComm, LinearMap.sub_apply, LinearMap.comp_apply, sub_apply]
  have hd : ∀ f : TestFunction N, coordinateDerivative i f x =
      fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)) := fun f =>
    SchwartzMap.lineDerivOp_apply_eq_fderiv _ f x
  have hmul : fderiv ℝ ((multiplierOperator g u : TestFunction N)) x = fderiv ℝ
      (fun y => g y * u y) x := by
    congr 1; funext y; exact multiplierOperator_apply g u y
  rw [hd (multiplierOperator g u), multiplierOperator_apply g (coordinateDerivative i u),
    multiplierOperator_apply (coordinateDerivative i g) u, hmul,
    fderiv_fun_mul (g.differentiableAt) (u.differentiableAt), hd u, hd g]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring


/-! Order facts. -/

theorem fourierWeightENN_mono {s s' : ℝ} (h : s ≤ s') (u : TestFunction N) (ξ : Carrier N) :
    fourierWeightENN s u ξ ≤ fourierWeightENN s' u ξ := by
  unfold fourierWeightENN
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_le (one_le_japBracket ξ) h)) le_rfl

theorem sobolevNorm_mono {s s' : ℝ} (h : s ≤ s') (u : TestFunction N) :
    sobolevNorm s u ≤ sobolevNorm s' u := by
  have := ofReal_sobolevNorm_le_of_sq (s₁ := s) (s₂ := s') (u := u) (v := u) (K := 1)
    ENNReal.one_ne_top (by
      simp only [one_pow, one_mul]
      exact lintegral_mono fun ξ => pow_le_pow_left' (fourierWeightENN_mono h u ξ) 2)
  simpa using this

theorem HasOrder.mono {m m' : ℝ} {T : Operator N} (hT : HasOrder m T) (h : m ≤ m') :
    HasOrder m' T := by
  intro s
  obtain ⟨C, hC⟩ := hT s
  exact ⟨C, fun u => (hC u).trans (mul_le_mul_of_nonneg_left
    (sobolevNorm_mono (by linarith) u) C.2)⟩

/-- Multiplication by a Schwartz function has order zero. -/
theorem hasOrder_multiplierOperator_zero (g : TestFunction N) :
    HasOrder 0 (multiplierOperator g) := by
  apply hasOrder_of_kernelBound
  intro s
  set κ : Carrier N → ℝ := fun a => ‖a‖ ^ 0 * (peetreOmega a ^ |s| * ‖𝓕 g a‖) with hκdef
  have hint : Integrable κ := integrable_kernelWeight (𝓕 g) 0 |s|
  have hκc : Continuous κ :=
    (continuous_norm.pow 0).mul ((continuous_peetreOmega_rpow _).mul (𝓕 g).continuous.norm)
  have hκ0 : ∀ a, 0 ≤ κ a := fun a => by
    have := Real.rpow_nonneg (peetreOmega_pos a).le |s|
    simp only [hκdef]; positivity
  refine ⟨fun a => ENNReal.ofReal (κ a), ENNReal.measurable_ofReal.comp hκc.measurable,
    lintegral_ofReal_ne_top_of_integrable hint, fun u ξ => ?_⟩
  refine fw_le_single s 0 _ u ξ _ (fourier_mul_apply g u ξ) κ hκ0 fun a => ?_
  rw [norm_mul, add_zero]
  have hp := peetre_jap ξ (ξ - a) s
  rw [sub_sub_cancel] at hp
  have h1 := Real.rpow_nonneg (japBracket_pos (ξ - a)).le s
  have hg := norm_nonneg (𝓕 g a)
  have hu := norm_nonneg (𝓕 u (ξ - a))
  calc japBracket ξ ^ s * (‖𝓕 g a‖ * ‖𝓕 u (ξ - a)‖)
      ≤ (japBracket (ξ - a) ^ s * peetreOmega a ^ |s|) * (‖𝓕 g a‖ * ‖𝓕 u (ξ - a)‖) :=
        mul_le_mul_of_nonneg_right hp (mul_nonneg hg hu)
    _ = _ := by simp only [hκdef]; ring

/-- A coordinate derivative has order one. -/
theorem hasOrder_coordinateDerivative (i : Fin N) : HasOrder 1 (coordinateDerivative i) := by
  intro s
  refine ⟨(ENNReal.ofReal (2 * Real.pi)).toNNReal, fun u => ?_⟩
  have hK : ENNReal.ofReal (2 * Real.pi) ≠ ⊤ := ENNReal.ofReal_ne_top
  have key : ∫⁻ ξ, fourierWeightENN s (coordinateDerivative i u) ξ ^ 2 ≤
      ENNReal.ofReal (2 * Real.pi) ^ 2 * ∫⁻ ξ, fourierWeightENN (s + 1) u ξ ^ 2 := by
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top hK)]
    refine lintegral_mono fun ξ => ?_
    rw [← mul_pow]
    refine pow_le_pow_left' ?_ 2
    unfold fourierWeightENN
    rw [fourier_coordinateDerivative, enorm_mul]
    have hJ := Real.rpow_nonneg (japBracket_pos ξ).le s
    have e1 : ‖(2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ))‖ₑ = ENNReal.ofReal (2 * Real.pi * |ξ i|) := by
      rw [← ofReal_norm]
      congr 1
      simp [abs_of_pos Real.pi_pos]
    rw [e1, ← mul_assoc, ← ENNReal.ofReal_mul hJ]
    rw [← mul_assoc (ENNReal.ofReal (2 * Real.pi)),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have hξ : |ξ i| ≤ japBracket ξ := by
      refine le_trans ?_ (norm_le_japBracket ξ)
      simpa using PiLp.norm_apply_le ξ i
    rw [Real.rpow_add (japBracket_pos ξ), Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hξ (mul_nonneg hJ Real.pi_pos.le)]
  simpa [ENNReal.coe_toNNReal hK, ENNReal.coe_toNNReal_eq_toReal] using
    ofReal_sobolevNorm_le_of_sq hK key

end Hormander.B

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.RegularizedSign
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ}

/-- The order-zero bound controls the absolute integral against
every smooth compact cutoff between zero and one. This proves the
regularized-sign limiting argument before compact exhaustion
(BB Thm 6.3, p. 251). -/
theorem integral_cutoff_abs_le_orderZero_bound
    (Ω : Opens (Fin N → ℝ))
    {γ : (Fin N → ℝ) → ℝ} (hγ : ContDiffOn ℝ (⊤ : ℕ∞) γ (Ω : Set (Fin N → ℝ)))
    (T : TestFunction Ω ℝ (⊤ : ℕ∞) →ₗ[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ, |T φ| ≤ C * ‖(TestFunction.toBoundedContinuousFunctionCLM ℝ) φ‖)
    (hrep : ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞), (∫ x, γ x * φ x) = T φ)
    (χ : TestFunction Ω ℝ (⊤ : ℕ∞)) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    (∫ x, χ x * |γ x|) ≤ C := by
  let F (ε : ℝ) (x : Fin N → ℝ) :=
    γ x * (χ x * (γ x / Real.sqrt ((γ x) ^ 2 + ε ^ 2)))
  have hloc : LocallyIntegrableOn γ (Ω : Set (Fin N → ℝ)) volume :=
    hγ.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hI : Integrable (fun x => χ x * |γ x|) := by
    simpa only [smul_eq_mul, Real.norm_eq_abs] using χ.integrable_smul hloc.norm
  have hm {ε : ℝ} (hε : 0 < ε) : AEStronglyMeasurable (F ε) volume := by
    let φ := regularizedSignTest Ω hγ hε χ
    have H := φ.integrable_smul hloc
    have he : (fun x => φ x • γ x) = F ε := by
      funext x
      change (χ x * (γ x / Real.sqrt ((γ x) ^ 2 + ε ^ 2))) * γ x = _
      dsimp only [F]
      ring
    rw [he] at H
    exact H.aestronglyMeasurable
  have hb {ε : ℝ} (hε : 0 < ε) : ∀ x, ‖F ε x‖ ≤ χ x * |γ x| := by
    intro x
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hχ x).1]
    calc
      |γ x| * (χ x * |γ x / Real.sqrt ((γ x) ^ 2 + ε ^ 2)|) =
          (χ x * |γ x|) * |γ x / Real.sqrt ((γ x) ^ 2 + ε ^ 2)| := by ring
      _ ≤ (χ x * |γ x|) * 1 := mul_le_mul_of_nonneg_left
        (abs_regularizedSign_le_one (γ x) hε) (mul_nonneg (hχ x).1 (abs_nonneg _))
      _ = χ x * |γ x| := mul_one _
  have ht (x : Fin N → ℝ) : Tendsto (fun ε : ℝ => F ε x)
      (𝓝[>] 0) (𝓝 (χ x * |γ x|)) := by
    by_cases hx : γ x = 0
    · simp only [F, hx, zero_mul, abs_zero, mul_zero]
      exact tendsto_const_nhds
    · have hne : Real.sqrt ((γ x) ^ 2 + (0 : ℝ) ^ 2) ≠ 0 := by
        simpa only [zero_pow (by norm_num : 2 ≠ 0), add_zero, Real.sqrt_sq_eq_abs]
          using abs_ne_zero.mpr hx
      have hden : ContinuousAt (fun ε : ℝ => Real.sqrt ((γ x) ^ 2 + ε ^ 2)) 0 :=
        Real.continuous_sqrt.continuousAt.comp (continuousAt_const.add (continuousAt_id.pow 2))
      have hcont : ContinuousAt (fun ε : ℝ => F ε x) 0 :=
        continuousAt_const.mul (continuousAt_const.mul (continuousAt_const.div hden hne))
      have he : F 0 x = χ x * |γ x| := by
        dsimp only [F]
        rw [zero_pow (by norm_num : 2 ≠ 0), add_zero, Real.sqrt_sq_eq_abs]
        calc
          γ x * (χ x * (γ x / |γ x|)) = χ x * ((γ x) ^ 2 / |γ x|) := by ring
          _ = χ x * (|γ x| ^ 2 / |γ x|) := by rw [sq_abs]
          _ = χ x * |γ x| := by rw [pow_two, mul_div_cancel_right₀ _ (abs_ne_zero.mpr hx)]
      rw [← he]
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have H := tendsto_integral_filter_of_dominated_convergence (fun x => χ x * |γ x|)
    (by filter_upwards [self_mem_nhdsWithin] with ε hε; exact hm hε)
    (by filter_upwards [self_mem_nhdsWithin] with ε hε; exact Eventually.of_forall (hb hε))
    hI (Eventually.of_forall ht)
  apply le_of_tendsto H
  filter_upwards [self_mem_nhdsWithin] with ε hε
  let φ := regularizedSignTest Ω hγ hε χ
  have he : F ε = fun x => γ x * φ x := rfl
  rw [he, hrep]
  exact (le_abs_self (T φ)).trans ((hbound φ).trans
    ((mul_le_mul_of_nonneg_left (norm_regularizedSignTest_le_one Ω hγ hε χ hχ) hC).trans_eq
      (mul_one C)))

end RothschildStein.H1

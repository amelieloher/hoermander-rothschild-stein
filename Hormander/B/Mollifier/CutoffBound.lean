-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Mollifier.Cutoff

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace Hormander.B

variable {N : ℕ}

/-- (uniform contraction, Fourier form) The mollifier is a uniform contraction on every
Sobolev level for Schwartz functions. -/
theorem uniformOrder_mollOp : UniformOrder 0 (fun d : PosScale => mollOpS N d) := by
  intro s
  refine ⟨1, fun d u => ?_⟩
  have key : ∫⁻ ξ, fourierWeightENN s (mollOpS N d u) ξ ^ 2 ≤
      (1 : ℝ≥0∞) ^ 2 * ∫⁻ ξ, fourierWeightENN (s + 0) u ξ ^ 2 := by
    rw [one_pow, one_mul, add_zero]
    refine lintegral_mono fun ξ => pow_le_pow_left' ?_ 2
    unfold fourierWeightENN
    refine mul_le_mul' le_rfl ?_
    change ‖𝓕 (mollOp N d.1 d.2 u) ξ‖ₑ ≤ _
    rw [fourier_mollOp, enorm_mul]
    calc ‖mollSymbol N d.1 d.2 ξ‖ₑ * ‖𝓕 u ξ‖ₑ ≤ 1 * ‖𝓕 u ξ‖ₑ := by
          refine mul_le_mul' ?_ le_rfl
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_one.2 (norm_mollSymbol_le d.1 d.2 ξ)
      _ = _ := one_mul _
  simpa using ofReal_sobolevNorm_le_of_sq (K := 1) ENNReal.one_ne_top key

theorem UniformOrder.sub {ι : Type*} {m : ℝ} {T U : ι → Operator N} (hT : UniformOrder m T)
    (hU : UniformOrder m U) : UniformOrder m (fun i => T i - U i) := by
  have := hT.add (hU.smul (-1 : ℂ))
  convert this using 2 with i
  simp [sub_eq_add_neg]

/-- Nested-cutoff order-zero mollifier commutators, uniformly in `δ > 0`. -/
theorem mollifier_cutoff_commutator_bound (X : RealSchwartzVectorField N)
    (z1 z2 : SchwartzMap (Carrier N) ℝ)
    (hz : ∀ x ∈ tsupport (z1 : Carrier N → ℝ), z2 x = 1) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 < δ) (u : TestFunction N),
      (operatorComm ((mollOp N δ hδ).comp (realMultiplierOperator z1)) (vectorFieldOperator X) u =
        operatorComm ((mollOp N δ hδ).comp (realMultiplierOperator z1)) (vectorFieldOperator X)
          (realMultiplierOperator z2 u) ∧
       sobolevNorm s (operatorComm ((mollOp N δ hδ).comp (realMultiplierOperator z1))
          (vectorFieldOperator X) u) ≤ C * sobolevNorm s (realMultiplierOperator z2 u)) ∧
      (operatorComm (operatorComm ((mollOp N δ hδ).comp (realMultiplierOperator z1))
          (vectorFieldOperator X)) (vectorFieldOperator X) u =
        operatorComm (operatorComm ((mollOp N δ hδ).comp (realMultiplierOperator z1))
          (vectorFieldOperator X)) (vectorFieldOperator X) (realMultiplierOperator z2 u) ∧
       sobolevNorm s (operatorComm (operatorComm ((mollOp N δ hδ).comp
          (realMultiplierOperator z1)) (vectorFieldOperator X)) (vectorFieldOperator X) u) ≤
        C * sobolevNorm s (realMultiplierOperator z2 u)) := by
  set z1c := complexifyRealSchwartz z1
  have hM1 : HasOrder 0 (realMultiplierOperator z1) := hasOrder_multiplierOperator_zero z1c
  have hMv : HasOrder 0 (multiplierOperator (vectorFieldOperator X z1c)) :=
    hasOrder_multiplierOperator_zero _
  have hMw : HasOrder 0 (multiplierOperator (vectorFieldOperator X (vectorFieldOperator X z1c))) :=
    hasOrder_multiplierOperator_zero _
  have u1 := uniformOrder_comm_moll_vectorField X
  have u2 := uniformOrder_comm2_moll_vectorField X X
  have uS := uniformOrder_mollOp (N := N)
  have F1 : UniformOrder (0 + 0) (fun d : PosScale =>
      (operatorComm (mollOpS N d) (vectorFieldOperator X)).comp (realMultiplierOperator z1) -
        (mollOpS N d).comp (multiplierOperator (vectorFieldOperator X z1c))) :=
    (u1.comp_right hM1).sub (uS.comp_right hMv)
  have F2 : UniformOrder (0 + 0) (fun d : PosScale =>
      (operatorComm (operatorComm (mollOpS N d) (vectorFieldOperator X))
          (vectorFieldOperator X)).comp (realMultiplierOperator z1) -
        (2 : ℂ) • (operatorComm (mollOpS N d) (vectorFieldOperator X)).comp
          (multiplierOperator (vectorFieldOperator X z1c)) +
        (mollOpS N d).comp (multiplierOperator (vectorFieldOperator X (vectorFieldOperator X z1c)))) :=
    (((u2.comp_right hM1).sub ((u1.comp_right hMv).smul (2 : ℂ)))).add (uS.comp_right hMw)
  obtain ⟨C₁, h₁⟩ := F1 s
  obtain ⟨C₂, h₂⟩ := F2 s
  refine ⟨C₁ + C₂, by positivity, fun δ hδ u => ?_⟩
  obtain ⟨a1, a2⟩ := mollifier_cutoff_identity_first X z1 z2 hz δ hδ
  obtain ⟨b1, b2⟩ := mollifier_cutoff_identity_second X z1 z2 hz δ hδ
  have e1 : operatorComm ((mollOp N δ hδ).comp (realMultiplierOperator z1)) (vectorFieldOperator X) u =
      operatorComm ((mollOp N δ hδ).comp (realMultiplierOperator z1)) (vectorFieldOperator X)
        (realMultiplierOperator z2 u) := LinearMap.congr_fun a2 u
  have e2 : operatorComm (operatorComm ((mollOp N δ hδ).comp (realMultiplierOperator z1))
          (vectorFieldOperator X)) (vectorFieldOperator X) u =
        operatorComm (operatorComm ((mollOp N δ hδ).comp (realMultiplierOperator z1))
          (vectorFieldOperator X)) (vectorFieldOperator X) (realMultiplierOperator z2 u) :=
    LinearMap.congr_fun b2 u
  refine ⟨⟨e1, ?_⟩, ⟨e2, ?_⟩⟩
  · rw [e1, a1]
    have := h₁ ⟨δ, hδ⟩ (realMultiplierOperator z2 u)
    simp only [add_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_right (by simp) (norm_nonneg _))
  · rw [e2, b1]
    have := h₂ ⟨δ, hδ⟩ (realMultiplierOperator z2 u)
    simp only [add_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_right (by simp) (norm_nonneg _))

end Hormander.B

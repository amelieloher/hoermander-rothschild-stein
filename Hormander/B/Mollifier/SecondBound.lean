-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Mollifier.SecondFourier

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace Hormander.B

variable {N : ℕ}

/-- The combined coefficient of the double commutator. -/
def cK (δ : ℝ) (hδ : 0 < δ) (i k : Fin N) (ξ α β : Carrier N) : ℂ :=
  cT1 δ hδ i k ξ α β - cT2 δ hδ i k ξ α β - cT3 δ hδ i k ξ α β + cT4 δ hδ i k ξ α β

theorem bracket_identity (u0 u1 u2 u3 v0 v1 v2 v3 F0 F1 F2 F3 ai ak bi bk : ℂ)
    (hu1 : u1 = u0 - ai) (hu2 : u2 = u0 - bi) (hu3 : u3 = u0 - ai - bi)
    (hv1 : v1 = v0 - ak) (hv2 : v2 = v0 - bk) (hv3 : v3 = v0 - ak - bk) :
    u1 * v3 * (F0 - F1) - v2 * u3 * (F2 - F3) =
      (u0 * v0 * F0 - u1 * v1 * F1 - u2 * v2 * F2 + u3 * v3 * F3) -
        ak * (u0 * F0 - u3 * F3) - bk * (u0 * F0 - u1 * F1) - ai * (v0 * F0 - v2 * F2) +
        ai * (ak + bk) * F0 := by
  subst hu1 hu2 hu3 hv1 hv2 hv3
  ring

theorem cK_eq (δ : ℝ) (hδ : 0 < δ) (i k : Fin N) (ξ α β : Carrier N) :
    cK δ hδ i k ξ α β = (2 * Real.pi * Complex.I) ^ 2 *
      (coordC i (ξ - α) * coordC k (ξ - α - β) *
          (mollSymbol N δ hδ ξ - mollSymbol N δ hδ (ξ - α)) -
        coordC k (ξ - β) * coordC i (ξ - α - β) *
          (mollSymbol N δ hδ (ξ - β) - mollSymbol N δ hδ (ξ - α - β))) := by
  unfold cK cT1 cT2 cT3 cT4 derivSym
  ring

theorem real_sum_le (L L₂ p q X : ℝ) (hL : 0 ≤ L) (hL₂ : 0 ≤ L₂)
    (hpq : p * q ≤ X) (hpp : p * p ≤ X) :
    L₂ * (p * q) + p * (L * (p + q)) + q * (L * p) + p * (L * q) + p * (p + q) ≤
      (L₂ + 4 * L + 2) * X := by
  nlinarith [mul_le_mul_of_nonneg_left hpq hL₂, mul_le_mul_of_nonneg_left hpq hL,
    mul_le_mul_of_nonneg_left hpp hL]

theorem norm_cK_le (L L₂ : ℝ) (hL0 : 0 ≤ L) (hL₂0 : 0 ≤ L₂)
    (hL : ∀ (δ : ℝ) (hδ : 0 < δ) (i : Fin N) (ξ η : Carrier N),
      ‖coordC i ξ * mollSymbol N δ hδ ξ - coordC i η * mollSymbol N δ hδ η‖ ≤ L * ‖ξ - η‖)
    (hL₂ : ∀ (δ : ℝ) (hδ : 0 < δ) (i k : Fin N) (x d e : Carrier N),
      ‖coordC i (x + d + e) * coordC k (x + d + e) * mollSymbol N δ hδ (x + d + e) -
        coordC i (x + d) * coordC k (x + d) * mollSymbol N δ hδ (x + d) -
        coordC i (x + e) * coordC k (x + e) * mollSymbol N δ hδ (x + e) +
        coordC i x * coordC k x * mollSymbol N δ hδ x‖ ≤ L₂ * (‖d‖ * ‖e‖))
    (δ : ℝ) (hδ : 0 < δ) (i k : Fin N) (ξ α β : Carrier N) :
    ‖cK δ hδ i k ξ α β‖ ≤ (2 * Real.pi) ^ 2 * ((L₂ + 4 * L + 2) *
      (peetreOmega α ^ 2 * peetreOmega β ^ 2)) := by
  rw [cK_eq, norm_mul]
  have hn : ‖(2 * (Real.pi : ℂ) * Complex.I) ^ 2‖ = (2 * Real.pi) ^ 2 := by
    rw [norm_pow]; simp [abs_of_pos Real.pi_pos]
  rw [hn]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set x0 := ξ
  set x1 := ξ - α
  set x2 := ξ - β
  set x3 := ξ - α - β
  have hid := bracket_identity (coordC i x0) (coordC i x1) (coordC i x2) (coordC i x3)
    (coordC k x0) (coordC k x1) (coordC k x2) (coordC k x3)
    (mollSymbol N δ hδ x0) (mollSymbol N δ hδ x1) (mollSymbol N δ hδ x2) (mollSymbol N δ hδ x3)
    (coordC i α) (coordC k α) (coordC i β) (coordC k β)
    (by simp only [x1, x0, coordC_sub]) (by simp only [x2, x0, coordC_sub])
    (by simp only [x3, x0, coordC_sub]) (by simp only [x1, x0, coordC_sub])
    (by simp only [x2, x0, coordC_sub]) (by simp only [x3, x0, coordC_sub])
  rw [hid]
  have oa := one_le_peetreOmega α
  have ob := one_le_peetreOmega β
  have nα : ‖α‖ ≤ peetreOmega α := by
    refine (norm_le_japBracket α).trans ?_
    unfold peetreOmega
    nlinarith [japBracket_pos α, (by rw [Real.one_le_sqrt]; norm_num : (1:ℝ) ≤ Real.sqrt 2)]
  have nβ : ‖β‖ ≤ peetreOmega β := by
    refine (norm_le_japBracket β).trans ?_
    unfold peetreOmega
    nlinarith [japBracket_pos β, (by rw [Real.one_le_sqrt]; norm_num : (1:ℝ) ≤ Real.sqrt 2)]
  -- mixed difference
  have e0 : x3 + α + β = x0 := by simp only [x3, x0]; abel
  have e2 : x3 + α = x2 := by simp only [x3, x2]; abel
  have e1 : x3 + β = x1 := by simp only [x3, x1]; abel
  have hmix := hL₂ δ hδ i k x3 α β
  rw [e0, e2, e1] at hmix
  have h03 := hL δ hδ i x0 x3
  have h01 := hL δ hδ i x0 x1
  have h02 := hL δ hδ k x0 x2
  have n03 : ‖x0 - x3‖ ≤ ‖α‖ + ‖β‖ := by
    have : x0 - x3 = α + β := by simp only [x0, x3]; abel
    rw [this]; exact norm_add_le _ _
  have n01 : ‖x0 - x1‖ = ‖α‖ := by simp only [x0, x1, sub_sub_cancel]
  have n02 : ‖x0 - x2‖ = ‖β‖ := by simp only [x0, x2, sub_sub_cancel]
  have cα : ∀ j, ‖coordC j α‖ ≤ ‖α‖ := fun j => norm_coordC_le j α
  have cβ : ∀ j, ‖coordC j β‖ ≤ ‖β‖ := fun j => norm_coordC_le j β
  have m0 := norm_mollSymbol_le (N := N) δ hδ x0
  have t1 : ‖coordC k α * (coordC i x0 * mollSymbol N δ hδ x0 - coordC i x3 * mollSymbol N δ hδ x3)‖
      ≤ ‖α‖ * (L * (‖α‖ + ‖β‖)) := by
    rw [norm_mul]
    exact mul_le_mul (cα k) (h03.trans (mul_le_mul_of_nonneg_left n03 hL0)) (norm_nonneg _)
      (norm_nonneg _)
  have t2 : ‖coordC k β * (coordC i x0 * mollSymbol N δ hδ x0 - coordC i x1 * mollSymbol N δ hδ x1)‖
      ≤ ‖β‖ * (L * ‖α‖) := by
    rw [norm_mul]
    exact mul_le_mul (cβ k) (by rw [n01] at h01; exact h01) (norm_nonneg _) (norm_nonneg _)
  have t3 : ‖coordC i α * (coordC k x0 * mollSymbol N δ hδ x0 - coordC k x2 * mollSymbol N δ hδ x2)‖
      ≤ ‖α‖ * (L * ‖β‖) := by
    rw [norm_mul]
    exact mul_le_mul (cα i) (by rw [n02] at h02; exact h02) (norm_nonneg _) (norm_nonneg _)
  have t4 : ‖coordC i α * (coordC k α + coordC k β) * mollSymbol N δ hδ x0‖ ≤
      ‖α‖ * (‖α‖ + ‖β‖) := by
    rw [norm_mul, norm_mul]
    calc ‖coordC i α‖ * ‖coordC k α + coordC k β‖ * ‖mollSymbol N δ hδ x0‖
        ≤ ‖α‖ * (‖α‖ + ‖β‖) * 1 := by
          refine mul_le_mul (mul_le_mul (cα i) ((norm_add_le _ _).trans (add_le_add (cα k) (cβ k)))
            (norm_nonneg _) (norm_nonneg _)) m0 (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  have tri : ∀ (A B C D E : ℂ), ‖A - B - C - D + E‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖E‖ := by
    intro A B C D E
    calc ‖A - B - C - D + E‖ ≤ ‖A - B - C - D‖ + ‖E‖ := norm_add_le _ _
      _ ≤ ‖A - B - C‖ + ‖D‖ + ‖E‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖A - B‖ + ‖C‖ + ‖D‖ + ‖E‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ _ := by gcongr; exact norm_sub_le _ _
  refine (tri _ _ _ _ _).trans ?_
  have hA : ‖coordC i x0 * coordC k x0 * mollSymbol N δ hδ x0 -
      coordC i x1 * coordC k x1 * mollSymbol N δ hδ x1 -
      coordC i x2 * coordC k x2 * mollSymbol N δ hδ x2 +
      coordC i x3 * coordC k x3 * mollSymbol N δ hδ x3‖ ≤ L₂ * (‖α‖ * ‖β‖) := by
    have : coordC i x0 * coordC k x0 * mollSymbol N δ hδ x0 -
      coordC i x1 * coordC k x1 * mollSymbol N δ hδ x1 -
      coordC i x2 * coordC k x2 * mollSymbol N δ hδ x2 +
      coordC i x3 * coordC k x3 * mollSymbol N δ hδ x3 =
      coordC i x0 * coordC k x0 * mollSymbol N δ hδ x0 -
        coordC i x2 * coordC k x2 * mollSymbol N δ hδ x2 -
        coordC i x1 * coordC k x1 * mollSymbol N δ hδ x1 +
        coordC i x3 * coordC k x3 * mollSymbol N δ hδ x3 := by ring
    rw [this]; exact hmix
  have n0α := norm_nonneg α
  have n0β := norm_nonneg β
  have pab : ‖α‖ * ‖β‖ ≤ peetreOmega α ^ 2 * peetreOmega β ^ 2 := by
    have h1 : ‖α‖ * ‖β‖ ≤ peetreOmega α * peetreOmega β := mul_le_mul nα nβ n0β (by linarith)
    have h2 : peetreOmega α * peetreOmega β ≤ peetreOmega α ^ 2 * peetreOmega β ^ 2 := by
      have : peetreOmega α ≤ peetreOmega α ^ 2 := by nlinarith
      have : peetreOmega β ≤ peetreOmega β ^ 2 := by nlinarith
      exact mul_le_mul ‹peetreOmega α ≤ _› this (by linarith) (by positivity)
    exact h1.trans h2
  have paa : ‖α‖ * ‖α‖ ≤ peetreOmega α ^ 2 * peetreOmega β ^ 2 := by
    have h1 : ‖α‖ * ‖α‖ ≤ peetreOmega α ^ 2 := by nlinarith
    have h2 : (1 : ℝ) ≤ peetreOmega β ^ 2 := by nlinarith
    nlinarith [sq_nonneg (peetreOmega α)]
  have hsum : L₂ * (‖α‖ * ‖β‖) + ‖α‖ * (L * (‖α‖ + ‖β‖)) + ‖β‖ * (L * ‖α‖) + ‖α‖ * (L * ‖β‖) +
      ‖α‖ * (‖α‖ + ‖β‖) ≤ (L₂ + 4 * L + 2) * (peetreOmega α ^ 2 * peetreOmega β ^ 2) := by
    exact real_sum_le L L₂ ‖α‖ ‖β‖ _ hL0 hL₂0 pab paa
  linarith [hA, t1, t2, t3, t4, hsum]

end Hormander.B

namespace Hormander.B

variable {N : ℕ}

theorem fourier_add_testFunction (f h : TestFunction N) : 𝓕 (f + h) = 𝓕 f + 𝓕 h := by
  simp

theorem fourier_comm2 (δ : ℝ) (hδ : 0 < δ) (a b u : TestFunction N) (i k : Fin N) (ξ : Carrier N) :
    𝓕 (operatorComm (operatorComm (mollOp N δ hδ) (DOp a i)) (DOp b k) u) ξ =
      ∫ α, ∫ β, tripleIntegrand a b u ξ (cK δ hδ i k ξ) (α, β) := by
  obtain ⟨h1, h2, h3, h4⟩ := integrable_cT δ hδ a b u i k ξ
  have e : operatorComm (operatorComm (mollOp N δ hδ) (DOp a i)) (DOp b k) u =
      mollOp N δ hδ (DOp a i (DOp b k u)) - DOp a i (mollOp N δ hδ (DOp b k u)) -
        DOp b k (mollOp N δ hδ (DOp a i u)) + DOp b k (DOp a i (mollOp N δ hδ u)) := by
    simp only [operatorComm, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
    abel
  have hs : tripleIntegrand a b u ξ (cK δ hδ i k ξ) =
      fun p => tripleIntegrand a b u ξ (cT1 δ hδ i k ξ) p - tripleIntegrand a b u ξ (cT2 δ hδ i k ξ) p -
        tripleIntegrand a b u ξ (cT3 δ hδ i k ξ) p + tripleIntegrand a b u ξ (cT4 δ hδ i k ξ) p := by
    funext p
    simp only [tripleIntegrand, cK]
    ring
  have hI : Integrable (tripleIntegrand a b u ξ (cK δ hδ i k ξ)) (volume.prod volume) := by
    rw [hs]; exact ((h1.sub h2).sub h3).add h4
  rw [e, fourier_add_testFunction, fourier_sub_testFunction, fourier_sub_testFunction, add_apply, sub_apply, sub_apply,
    fourier_T1, fourier_T2, fourier_T3, fourier_T4, ← integral_prod _ h1, ← integral_prod _ h2,
    ← integral_prod _ h3, ← integral_prod _ h4, ← integral_prod _ hI, hs,
    ]
  set f1 := tripleIntegrand a b u ξ (cT1 δ hδ i k ξ)
  set f2 := tripleIntegrand a b u ξ (cT2 δ hδ i k ξ)
  set f3 := tripleIntegrand a b u ξ (cT3 δ hδ i k ξ)
  set f4 := tripleIntegrand a b u ξ (cT4 δ hδ i k ξ)
  have I12 : Integrable (fun z => f1 z - f2 z) (volume.prod volume) := h1.sub h2
  have I123 : Integrable (fun z => f1 z - f2 z - f3 z) (volume.prod volume) := I12.sub h3
  have K : ∫ z, (f1 z - f2 z - f3 z + f4 z) ∂(volume.prod volume) =
      ∫ z, f1 z ∂(volume.prod volume) - ∫ z, f2 z ∂(volume.prod volume) -
        ∫ z, f3 z ∂(volume.prod volume) + ∫ z, f4 z ∂(volume.prod volume) := by
    rw [integral_add I123 h4, integral_sub I12 h3, integral_sub h1 h2]
  exact K.symm

end Hormander.B

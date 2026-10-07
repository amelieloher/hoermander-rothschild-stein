-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Nested.FiniteDifferenceBound
public import Hormander.B.Fractional.CommutatorFourier
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped FourierTransform

namespace Hormander.B

variable {N : ℕ}

/-- Joint continuity of the reflected finite difference in the increments and the base point. -/
theorem continuous_fdiffs_neg (q : ℕ) {Φ : Carrier N → ℂ} (hΦ : Continuous Φ) :
    Continuous (fun p : (Fin q → Carrier N) × Carrier N => fdiffs q (fun i => -p.1 i) Φ p.2) := by
  induction q with
  | zero => exact hΦ.comp continuous_snd
  | succ q ih =>
    have hc : Continuous (fun p : (Fin (q + 1) → Carrier N) × Carrier N =>
        fdiffs q (fun i => -(Fin.tail p.1) i) Φ (p.2 + -p.1 0) -
          fdiffs q (fun i => -(Fin.tail p.1) i) Φ p.2) := by
      have htail : Continuous (fun p : (Fin (q + 1) → Carrier N) × Carrier N => Fin.tail p.1) :=
        (continuous_pi fun i => (continuous_apply i.succ).comp continuous_fst)
      have hshift : Continuous (fun p : (Fin (q + 1) → Carrier N) × Carrier N => p.2 + -p.1 0) :=
        continuous_snd.add ((continuous_apply 0).comp continuous_fst).neg
      exact (ih.comp (htail.prodMk hshift)).sub (ih.comp (htail.prodMk continuous_snd))
    exact hc

theorem crude_aux (c A B W P n1 n2 : ℝ) (hc : 0 ≤ c) (hP : 0 ≤ P) (hA : A ≤ B * W)
    (hB : B ≤ B * W) (h1 : n1 ≤ c * A * P) (h2 : n2 ≤ c * B * P) :
    n1 + n2 ≤ 2 * c * (B * (W * P)) := by
  have e1 : c * A * P ≤ c * (B * W) * P :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hc) hP
  have e2 : c * B * P ≤ c * (B * W) * P :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hc) hP
  nlinarith

/-- Crude bound for the reflected finite differences of the Bessel symbol. -/
theorem norm_fdiffs_besselSym_le (σ : ℝ) (q : ℕ) :
    ∀ (a : Fin q → Carrier N) (ζ : Carrier N),
      ‖fdiffs q (fun i => -a i) (besselSym σ) ζ‖ ≤
        2 ^ q * japBracket ζ ^ σ * ∏ i, peetreOmega (a i) ^ |σ| := by
  induction q with
  | zero => intro a ζ; simp [norm_besselSym]
  | succ q ih =>
    intro a ζ
    have e : fdiffs (q + 1) (fun i => -a i) (besselSym σ) ζ =
        fdiffs q (fun i => -(Fin.tail a) i) (besselSym σ) (ζ + -a 0) -
          fdiffs q (fun i => -(Fin.tail a) i) (besselSym σ) ζ := rfl
    rw [e, Fin.prod_univ_succ]
    have h1 := ih (Fin.tail a) (ζ + -a 0)
    have h2 := ih (Fin.tail a) ζ
    have hpe := peetre_jap (ζ + -a 0) ζ σ
    have hsub : ζ + -a 0 - ζ = -a 0 := by abel
    have hn : peetreOmega (-a 0) = peetreOmega (a 0) := by
      unfold peetreOmega japBracket bracketSq; rw [norm_neg]
    rw [hsub, hn] at hpe
    have hJ := Real.rpow_nonneg (japBracket_pos ζ).le σ
    have hω1 : 1 ≤ peetreOmega (a 0) ^ |σ| := one_le_peetreOmega_rpow (a 0) (abs_nonneg σ)
    have hP0 : 0 ≤ ∏ i : Fin q, peetreOmega (Fin.tail a i) ^ |σ| :=
      Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (peetreOmega_pos _).le _)
    have hB : japBracket ζ ^ σ ≤ japBracket ζ ^ σ * peetreOmega (a 0) ^ |σ| :=
      le_mul_of_one_le_right hJ hω1
    have key := crude_aux (2 ^ q) _ (japBracket ζ ^ σ) (peetreOmega (a 0) ^ |σ|)
      (∏ i : Fin q, peetreOmega (Fin.tail a i) ^ |σ|) _ _ (by positivity) hP0 hpe hB h1 h2
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ _ := key
      _ = _ := by simp only [Fin.tail]; ring

theorem integral_pi_zero (F : (Fin 0 → Carrier N) → ℂ) :
    ∫ a : Fin 0 → Carrier N, F a = F default := by
  have : (volume : Measure (Fin 0 → Carrier N)) = Measure.dirac default := by
    rw [volume_pi, Measure.pi_of_empty]
    congr 1
    exact Subsingleton.elim _ _
  rw [this, integral_dirac]

theorem integral_pi_succ_cons {n : ℕ} (F : (Fin (n + 1) → Carrier N) → ℂ) :
    ∫ a : Fin (n + 1) → Carrier N, F a =
      ∫ p : Carrier N × (Fin n → Carrier N), F (Fin.cons p.1 p.2) ∂(volume.prod volume) := by
  have := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => Carrier N) 0).symm
  rw [← this.integral_comp']
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  rw [Measure.volume_eq_prod]

/-- Fourier transform of the (complexified) real coefficient. -/
def coeffHat (g : SchwartzMap (Carrier N) ℝ) : TestFunction N := 𝓕 (complexifyRealSchwartz g)

/-- The nested commutator `[g₀, [g₁, … [g_{q-1}, Λ^σ]…]]` of `Λ^σ` with real multipliers. -/
def nestedComm (σ : ℝ) : (q : ℕ) → (Fin q → SchwartzMap (Carrier N) ℝ) → Operator N
  | 0, _ => lambdaOperator σ
  | q + 1, gs => operatorComm (realMultiplierOperator (gs 0)) (nestedComm σ q (Fin.tail gs))

/-- The integrand of the Fourier kernel, based at the output frequency `ξ`. -/
def repIntegrand (σ : ℝ) (q : ℕ) (gs : Fin q → SchwartzMap (Carrier N) ℝ) (u : TestFunction N)
    (ξ : Carrier N) (a : Fin q → Carrier N) : ℂ :=
  (∏ i, coeffHat (gs i) (a i)) * fdiffs q (fun i => -a i) (besselSym σ) ξ *
    𝓕 u (ξ - ∑ i, a i)

theorem continuous_repIntegrand (σ : ℝ) (q : ℕ) (gs : Fin q → SchwartzMap (Carrier N) ℝ)
    (u : TestFunction N) (ξ : Carrier N) : Continuous (repIntegrand σ q gs u ξ) := by
  unfold repIntegrand
  refine (continuous_finsetProd _ (fun i _ => (coeffHat (gs i)).continuous.comp
    (continuous_apply i))).mul ?_ |>.mul ?_
  · exact (continuous_fdiffs_neg q (continuous_besselSym σ)).comp (continuous_id.prodMk continuous_const)
  · exact (𝓕 u).continuous.comp (continuous_const.sub (continuous_finsetSum _ (fun i _ => continuous_apply i)))

/-- The weighted coefficient transform is integrable. -/
theorem integrable_coeffWeight (σ : ℝ) (g : SchwartzMap (Carrier N) ℝ) :
    Integrable (fun a : Carrier N => peetreOmega a ^ |σ| * ‖coeffHat g a‖) :=
  integrable_peetreOmega_mul (coeffHat g) |σ|

theorem integrable_pi_majorant (σ : ℝ) {q : ℕ} (gs : Fin q → SchwartzMap (Carrier N) ℝ) :
    Integrable (fun a : Fin q → Carrier N =>
      ∏ i, (peetreOmega (a i) ^ |σ| * ‖coeffHat (gs i) (a i)‖)) :=
  Integrable.fintype_prod (f := fun i a => peetreOmega a ^ |σ| * ‖coeffHat (gs i) a‖)
    (fun i => integrable_coeffWeight σ (gs i))

theorem exists_bound_fourier (u : TestFunction N) : ∃ U : ℝ, 0 ≤ U ∧ ∀ x, ‖𝓕 u x‖ ≤ U :=
  ⟨SchwartzMap.seminorm ℝ 0 0 (𝓕 u), by positivity, fun x => by
    simpa using SchwartzMap.norm_le_seminorm ℝ (𝓕 u) x⟩

/-- Pointwise bound of the Fourier-kernel integrand by a product of weighted coefficients. -/
theorem norm_repIntegrand_le (σ : ℝ) (q : ℕ) (gs : Fin q → SchwartzMap (Carrier N) ℝ)
    (u : TestFunction N) (ξ : Carrier N) {U : ℝ} (hU : ∀ x, ‖𝓕 u x‖ ≤ U) (a : Fin q → Carrier N) :
    ‖repIntegrand σ q gs u ξ a‖ ≤
      (2 ^ q * japBracket ξ ^ σ * U) * ∏ i, (peetreOmega (a i) ^ |σ| * ‖coeffHat (gs i) (a i)‖) := by
  unfold repIntegrand
  rw [norm_mul, norm_mul, norm_prod, Finset.prod_mul_distrib]
  have h1 := norm_fdiffs_besselSym_le σ q a ξ
  have h2 := hU (ξ - ∑ i, a i)
  have hn : 0 ≤ ∏ i, ‖coeffHat (gs i) (a i)‖ := Finset.prod_nonneg (fun i _ => norm_nonneg _)
  have hJ := Real.rpow_nonneg (japBracket_pos ξ).le σ
  have hω : 0 ≤ ∏ i, peetreOmega (a i) ^ |σ| :=
    Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (peetreOmega_pos _).le _)
  calc (∏ i, ‖coeffHat (gs i) (a i)‖) * ‖fdiffs q (fun i => -a i) (besselSym σ) ξ‖ *
        ‖𝓕 u (ξ - ∑ i, a i)‖
      ≤ (∏ i, ‖coeffHat (gs i) (a i)‖) * (2 ^ q * japBracket ξ ^ σ * ∏ i, peetreOmega (a i) ^ |σ|) * U := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hn) h2 (norm_nonneg _)
          (mul_nonneg hn (mul_nonneg (mul_nonneg (by positivity) hJ) hω))
    _ = _ := by ring

/-- First product integrand of the induction step: `ĝ₀(b) · rep_q(ξ-b)(a)`. -/
def stepI1 (σ : ℝ) (q : ℕ) (gs : Fin (q + 1) → SchwartzMap (Carrier N) ℝ) (u : TestFunction N)
    (ξ : Carrier N) (p : Carrier N × (Fin q → Carrier N)) : ℂ :=
  coeffHat (gs 0) p.1 * repIntegrand σ q (Fin.tail gs) u (ξ - p.1) p.2

/-- Second product integrand of the induction step. -/
def stepI2 (σ : ℝ) (q : ℕ) (gs : Fin (q + 1) → SchwartzMap (Carrier N) ℝ) (u : TestFunction N)
    (ξ : Carrier N) (p : Carrier N × (Fin q → Carrier N)) : ℂ :=
  coeffHat (gs 0) p.1 * ((∏ i, coeffHat (Fin.tail gs i) (p.2 i)) *
    fdiffs q (fun i => -p.2 i) (besselSym σ) ξ * 𝓕 u (ξ - ∑ i, p.2 i - p.1))

theorem repIntegrand_cons (σ : ℝ) (q : ℕ) (gs : Fin (q + 1) → SchwartzMap (Carrier N) ℝ)
    (u : TestFunction N) (ξ : Carrier N) (p : Carrier N × (Fin q → Carrier N)) :
    repIntegrand σ (q + 1) gs u ξ (Fin.cons p.1 p.2) = stepI1 σ q gs u ξ p - stepI2 σ q gs u ξ p := by
  unfold repIntegrand stepI1 stepI2
  rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have e : fdiffs (q + 1) (fun i => -(Fin.cons p.1 p.2 : Fin (q + 1) → Carrier N) i) (besselSym σ) ξ =
      fdiffs q (fun i => -p.2 i) (besselSym σ) (ξ + -p.1) -
        fdiffs q (fun i => -p.2 i) (besselSym σ) ξ := rfl
  rw [e]
  have e4 : ξ + -p.1 = ξ - p.1 := by abel
  rw [e4]
  simp only [Fin.tail, repIntegrand]
  have e5 : ξ - (p.1 + ∑ x : Fin q, p.2 x) = ξ - ∑ x : Fin q, p.2 x - p.1 := by abel
  have e6 : ξ - p.1 - ∑ x : Fin q, p.2 x = ξ - ∑ x : Fin q, p.2 x - p.1 := by abel
  rw [e5, e6]
  ring

theorem continuous_stepI1 (σ : ℝ) (q : ℕ) (gs : Fin (q + 1) → SchwartzMap (Carrier N) ℝ)
    (u : TestFunction N) (ξ : Carrier N) : Continuous (stepI1 σ q gs u ξ) := by
  unfold stepI1 repIntegrand
  refine ((coeffHat (gs 0)).continuous.comp continuous_fst).mul ?_
  refine (Continuous.mul ?_ ?_).mul ?_
  · exact continuous_finsetProd _ (fun i _ => (coeffHat (Fin.tail gs i)).continuous.comp
      ((continuous_apply i).comp continuous_snd))
  · exact (continuous_fdiffs_neg q (continuous_besselSym σ)).comp
      (continuous_snd.prodMk (continuous_const.sub continuous_fst))
  · exact (𝓕 u).continuous.comp ((continuous_const.sub continuous_fst).sub
      (continuous_finsetSum _ (fun i _ => (continuous_apply i).comp continuous_snd)))

theorem continuous_stepI2 (σ : ℝ) (q : ℕ) (gs : Fin (q + 1) → SchwartzMap (Carrier N) ℝ)
    (u : TestFunction N) (ξ : Carrier N) : Continuous (stepI2 σ q gs u ξ) := by
  unfold stepI2
  refine ((coeffHat (gs 0)).continuous.comp continuous_fst).mul ?_
  refine (Continuous.mul ?_ ?_).mul ?_
  · exact continuous_finsetProd _ (fun i _ => (coeffHat (Fin.tail gs i)).continuous.comp
      ((continuous_apply i).comp continuous_snd))
  · exact (continuous_fdiffs_neg q (continuous_besselSym σ)).comp
      (continuous_snd.prodMk continuous_const)
  · exact (𝓕 u).continuous.comp ((continuous_const.sub
      (continuous_finsetSum _ (fun i _ => (continuous_apply i).comp continuous_snd))).sub
      continuous_fst)

theorem norm_peetre_shift_le (σ : ℝ) (ξ b : Carrier N) :
    japBracket (ξ - b) ^ σ ≤ japBracket ξ ^ σ * peetreOmega b ^ |σ| := by
  have h := peetre_jap (ξ - b) ξ σ
  have hn : peetreOmega (-b) = peetreOmega b := by
    unfold peetreOmega japBracket bracketSq; rw [norm_neg]
  rwa [sub_sub_cancel_left, hn] at h

theorem integrable_stepI1 (σ : ℝ) (q : ℕ) (gs : Fin (q + 1) → SchwartzMap (Carrier N) ℝ)
    (u : TestFunction N) (ξ : Carrier N) :
    Integrable (stepI1 σ q gs u ξ) (volume.prod volume) := by
  obtain ⟨U, hU0, hU⟩ := exists_bound_fourier u
  have hmaj := (integrable_coeffWeight σ (gs 0)).mul_prod (integrable_pi_majorant σ (Fin.tail gs))
  refine (hmaj.const_mul (2 ^ q * japBracket ξ ^ σ * U)).mono'
    (continuous_stepI1 σ q gs u ξ).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  unfold stepI1
  rw [norm_mul]
  have h1 := norm_repIntegrand_le σ q (Fin.tail gs) u (ξ - p.1) hU p.2
  have h2 := norm_peetre_shift_le σ ξ p.1
  have hpr : 0 ≤ ∏ i, (peetreOmega (p.2 i) ^ |σ| * ‖coeffHat (Fin.tail gs i) (p.2 i)‖) :=
    Finset.prod_nonneg (fun i _ => mul_nonneg (Real.rpow_nonneg (peetreOmega_pos _).le _) (norm_nonneg _))
  have hJ := Real.rpow_nonneg (japBracket_pos ξ).le σ
  calc ‖coeffHat (gs 0) p.1‖ * ‖repIntegrand σ q (Fin.tail gs) u (ξ - p.1) p.2‖
      ≤ ‖coeffHat (gs 0) p.1‖ * ((2 ^ q * japBracket (ξ - p.1) ^ σ * U) *
          ∏ i, (peetreOmega (p.2 i) ^ |σ| * ‖coeffHat (Fin.tail gs i) (p.2 i)‖)) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ ‖coeffHat (gs 0) p.1‖ * ((2 ^ q * (japBracket ξ ^ σ * peetreOmega p.1 ^ |σ|) * U) *
          ∏ i, (peetreOmega (p.2 i) ^ |σ| * ‖coeffHat (Fin.tail gs i) (p.2 i)‖)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_right _ hpr
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) hU0
    _ = _ := by ring

theorem integrable_stepI2 (σ : ℝ) (q : ℕ) (gs : Fin (q + 1) → SchwartzMap (Carrier N) ℝ)
    (u : TestFunction N) (ξ : Carrier N) :
    Integrable (stepI2 σ q gs u ξ) (volume.prod volume) := by
  obtain ⟨U, hU0, hU⟩ := exists_bound_fourier u
  have hmaj := (integrable_coeffWeight σ (gs 0)).mul_prod (integrable_pi_majorant σ (Fin.tail gs))
  refine (hmaj.const_mul (2 ^ q * japBracket ξ ^ σ * U)).mono'
    (continuous_stepI2 σ q gs u ξ).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  unfold stepI2
  rw [norm_mul, norm_mul, norm_mul, norm_prod]
  have h1 := norm_fdiffs_besselSym_le σ q p.2 ξ
  have h2 := hU (ξ - ∑ i, p.2 i - p.1)
  have hω1 : 1 ≤ peetreOmega p.1 ^ |σ| := one_le_peetreOmega_rpow p.1 (abs_nonneg σ)
  have hJ := Real.rpow_nonneg (japBracket_pos ξ).le σ
  have hn : 0 ≤ ∏ i, ‖coeffHat (Fin.tail gs i) (p.2 i)‖ := Finset.prod_nonneg (fun i _ => norm_nonneg _)
  have hω : 0 ≤ ∏ i, peetreOmega (p.2 i) ^ |σ| :=
    Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (peetreOmega_pos _).le _)
  have hc : 0 ≤ ‖coeffHat (gs 0) p.1‖ := norm_nonneg _
  have step : (∏ i, ‖coeffHat (Fin.tail gs i) (p.2 i)‖) *
        ‖fdiffs q (fun i => -p.2 i) (besselSym σ) ξ‖ * ‖𝓕 u (ξ - ∑ i, p.2 i - p.1)‖ ≤
      (∏ i, ‖coeffHat (Fin.tail gs i) (p.2 i)‖) *
        (2 ^ q * japBracket ξ ^ σ * ∏ i, peetreOmega (p.2 i) ^ |σ|) * U :=
    mul_le_mul (mul_le_mul_of_nonneg_left h1 hn) h2 (norm_nonneg _)
      (mul_nonneg hn (mul_nonneg (mul_nonneg (by positivity) hJ) hω))
  calc ‖coeffHat (gs 0) p.1‖ * ((∏ i, ‖coeffHat (Fin.tail gs i) (p.2 i)‖) *
        ‖fdiffs q (fun i => -p.2 i) (besselSym σ) ξ‖ * ‖𝓕 u (ξ - ∑ i, p.2 i - p.1)‖)
      ≤ ‖coeffHat (gs 0) p.1‖ * ((∏ i, ‖coeffHat (Fin.tail gs i) (p.2 i)‖) *
        (2 ^ q * japBracket ξ ^ σ * ∏ i, peetreOmega (p.2 i) ^ |σ|) * U) :=
        mul_le_mul_of_nonneg_left step hc
    _ = (2 ^ q * japBracket ξ ^ σ * U) * (‖coeffHat (gs 0) p.1‖ *
        ∏ i, (peetreOmega (p.2 i) ^ |σ| * ‖coeffHat (Fin.tail gs i) (p.2 i)‖)) := by
        rw [Finset.prod_mul_distrib]; ring
    _ ≤ (2 ^ q * japBracket ξ ^ σ * U) * ((peetreOmega p.1 ^ |σ| * ‖coeffHat (gs 0) p.1‖) *
        ∏ i, (peetreOmega (p.2 i) ^ |σ| * ‖coeffHat (Fin.tail gs i) (p.2 i)‖)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun i _ =>
          mul_nonneg (Real.rpow_nonneg (peetreOmega_pos _).le _) (norm_nonneg _)))
        nlinarith

theorem fourier_realMultiplier (g : SchwartzMap (Carrier N) ℝ) (u : TestFunction N) (ξ : Carrier N) :
    𝓕 (realMultiplierOperator g u) ξ = ∫ b, coeffHat g b * 𝓕 u (ξ - b) :=
  fourier_mul_apply (complexifyRealSchwartz g) u ξ

/-- The Fourier transform of the nested multiplier commutator of `Λ^σ`, as an integral over
the increments with the reflected finite difference of the Bessel symbol. -/
theorem fourier_nestedComm (σ : ℝ) : ∀ (q : ℕ) (gs : Fin q → SchwartzMap (Carrier N) ℝ)
    (u : TestFunction N) (ξ : Carrier N),
    𝓕 (nestedComm σ q gs u) ξ = ∫ a, repIntegrand σ q gs u ξ a := by
  intro q
  induction q with
  | zero =>
    intro gs u ξ
    rw [integral_pi_zero]
    simp [nestedComm, fourier_lambdaOperator, repIntegrand]
  | succ q ih =>
    intro gs u ξ
    have e : nestedComm σ (q + 1) gs u = realMultiplierOperator (gs 0) (nestedComm σ q (Fin.tail gs) u) -
        nestedComm σ q (Fin.tail gs) (realMultiplierOperator (gs 0) u) := rfl
    rw [e, fourier_sub_testFunction, sub_apply]
    have hT1 : 𝓕 (realMultiplierOperator (gs 0) (nestedComm σ q (Fin.tail gs) u)) ξ =
        ∫ b, ∫ a, stepI1 σ q gs u ξ (b, a) := by
      rw [fourier_realMultiplier]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      rw [ih (Fin.tail gs) u (ξ - b), ← integral_const_mul]
      rfl
    have hT2 : 𝓕 (nestedComm σ q (Fin.tail gs) (realMultiplierOperator (gs 0) u)) ξ =
        ∫ a, ∫ b, stepI2 σ q gs u ξ (b, a) := by
      rw [ih (Fin.tail gs) _ ξ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      simp only [repIntegrand]
      rw [fourier_realMultiplier, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only [stepI2]
      ring
    have hI1 := integrable_stepI1 σ q gs u ξ
    have hI2 := integrable_stepI2 σ q gs u ξ
    have hI2' : Integrable (Function.uncurry fun (a : Fin q → Carrier N) (b : Carrier N) =>
        stepI2 σ q gs u ξ (b, a)) (volume.prod volume) := by
      have := hI2.swap
      exact this
    rw [hT1, hT2, integral_integral_swap hI2', integral_pi_succ_cons]
    have hc : (fun p : Carrier N × (Fin q → Carrier N) =>
        repIntegrand σ (q + 1) gs u ξ (Fin.cons p.1 p.2)) =
        fun p => stepI1 σ q gs u ξ p - stepI2 σ q gs u ξ p :=
      funext fun p => repIntegrand_cons σ q gs u ξ p
    rw [hc, integral_sub hI1 hI2, integral_prod _ hI1, integral_prod _ hI2]

end Hormander.B

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Nested.Representation
public import Hormander.B.Nested.IteratedYoung

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap ENNReal
open scoped FourierTransform ENNReal

namespace Hormander.B

variable {N : ℕ}

theorem besselSym_eq_ofReal (σ : ℝ) :
    besselSym (N := N) σ = fun x => Complex.ofRealCLM (bracketPow σ x) := rfl

theorem norm_fdiffs_besselSym_eq (σ : ℝ) (q : ℕ) (a : Fin q → Carrier N) (η : Carrier N) :
    ‖fdiffs q a (besselSym σ) η‖ = ‖fdiffs q a (bracketPow σ) η‖ := by
  rw [besselSym_eq_ofReal, fdiffs_map Complex.ofRealCLM q a (bracketPow σ) η]
  simp

theorem norm_fdiffs_neg_eq (σ : ℝ) (q : ℕ) (a : Fin q → Carrier N) (ξ : Carrier N) :
    ‖fdiffs q (fun i => -a i) (besselSym σ) ξ‖ =
      ‖fdiffs q a (bracketPow σ) (ξ - ∑ i, a i)‖ := by
  rw [fdiffs_neg, norm_smul, norm_fdiffs_besselSym_eq]
  simp


/-- The real kernel attached to a coefficient: `‖a‖ ⟨a⟩^M |ĝ(a)|`. -/
def coeffKernel (M : ℝ) (g : SchwartzMap (Carrier N) ℝ) (a : Carrier N) : ℝ :=
  ‖a‖ * (peetreOmega a ^ M * ‖coeffHat g a‖)

theorem coeffKernel_nonneg (M : ℝ) (g : SchwartzMap (Carrier N) ℝ) (a : Carrier N) :
    0 ≤ coeffKernel M g a :=
  mul_nonneg (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg (peetreOmega_pos _).le _) (norm_nonneg _))

theorem integrable_coeffKernel (M : ℝ) (g : SchwartzMap (Carrier N) ℝ) :
    Integrable (coeffKernel M g) := by
  have := integrable_kernelWeight (coeffHat g) 1 M
  simp only [pow_one] at this
  exact this

theorem continuous_coeffKernel (M : ℝ) (g : SchwartzMap (Carrier N) ℝ) :
    Continuous (coeffKernel M g) := by
  unfold coeffKernel
  have h1 : Continuous fun a : Carrier N => peetreOmega a ^ M := by
    have hc : Continuous fun a : Carrier N => peetreOmega a := by
      unfold peetreOmega japBracket bracketSq
      fun_prop
    exact hc.rpow_const fun a => Or.inl (peetreOmega_pos a).ne'
  exact continuous_norm.mul (h1.mul (coeffHat g).continuous.norm)

theorem weighted_aux (Ce Ks Jx Js Jσ Ωs Jp A P U D Kp : ℝ) (hCe : 0 ≤ Ce) (hKs : 0 ≤ Ks)
    (hJs : 0 ≤ Js) (hJσ : 0 ≤ Jσ) (hΩs : 0 ≤ Ωs) (_hJp : 0 ≤ Jp) (_hA : 0 ≤ A) (hP : 0 ≤ P)
    (hU : 0 ≤ U) (hD : 0 ≤ D)
    (h2 : Jx ≤ Js * (Ks * Ωs)) (h1 : D ≤ Ce * (A * Jσ * Jp)) (hker : A * P * (Ωs * Jp) ≤ Kp) :
    Jx * (P * D * U) ≤ (Ce * Ks) * Kp * ((Js * Jσ) * U) := by
  have hstep : P * D * U ≤ P * (Ce * (A * Jσ * Jp)) * U :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hP) hU
  have h3 : Jx * (P * D * U) ≤ (Js * (Ks * Ωs)) * (P * (Ce * (A * Jσ * Jp)) * U) :=
    mul_le_mul h2 hstep (by positivity) (by positivity)
  have h4 : (Js * (Ks * Ωs)) * (P * (Ce * (A * Jσ * Jp)) * U) =
      (Ce * Ks) * (A * P * (Ωs * Jp)) * ((Js * Jσ) * U) := by ring
  have h5 : (Ce * Ks) * (A * P * (Ωs * Jp)) * ((Js * Jσ) * U) ≤ (Ce * Ks) * Kp * ((Js * Jσ) * U) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hker (mul_nonneg hCe hKs))
      (mul_nonneg (mul_nonneg hJs hJσ) hU)
  linarith

/-- The pointwise weighted bound for the Fourier-kernel integrand (product Peetre weights). -/
theorem weighted_rep_bound (σ : ℝ) (q : ℕ) (s : ℝ) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (gs : Fin q → SchwartzMap (Carrier N) ℝ) (u : TestFunction N)
      (ξ : Carrier N) (a : Fin q → Carrier N),
      japBracket ξ ^ s * ‖repIntegrand σ q gs u ξ a‖ ≤
        Cc * (∏ i, coeffKernel (|σ - q| + |s|) (gs i) (a i)) *
          (japBracket (ξ - ∑ i, a i) ^ (s + σ - q) * ‖𝓕 u (ξ - ∑ i, a i)‖) := by
  obtain ⟨Ce, hCe, hE⟩ := finite_difference_bound (N := N) q σ
  refine ⟨Ce * (Real.sqrt 2 * 2 ^ q) ^ |s|, by positivity, fun gs u ξ a => ?_⟩
  set η : Carrier N := ξ - ∑ i, a i with hη
  have hnorm : ‖repIntegrand σ q gs u ξ a‖ =
      (∏ i, ‖coeffHat (gs i) (a i)‖) * ‖fdiffs q a (bracketPow σ) η‖ * ‖𝓕 u η‖ := by
    unfold repIntegrand
    rw [norm_mul, norm_mul, norm_prod, norm_fdiffs_neg_eq]
  have h1 := hE η a
  have h2 : japBracket ξ ^ s ≤
      japBracket η ^ s * ((Real.sqrt 2 * 2 ^ q) ^ |s| * ∏ i, peetreOmega (a i) ^ |s|) := by
    have hp := peetre_jap ξ η s
    have hsub : ξ - η = ∑ i, a i := by rw [hη]; abel
    rw [hsub] at hp
    have hs := peetreOmega_sum_le q (fun _ => (1 : ℝ)) (fun _ => ⟨zero_le_one, le_rfl⟩) a
    simp only [one_smul] at hs
    refine hp.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (japBracket_pos _).le _))
    calc peetreOmega (∑ i, a i) ^ |s| ≤ (Real.sqrt 2 * 2 ^ q * ∏ i, peetreOmega (a i)) ^ |s| :=
          Real.rpow_le_rpow (peetreOmega_pos _).le hs (abs_nonneg s)
      _ = _ := by
          rw [Real.mul_rpow (by positivity) (Finset.prod_nonneg (fun i _ => (peetreOmega_pos _).le)),
            Real.finsetProd_rpow _ _ (fun i _ => (peetreOmega_pos _).le)]
  have hJη := Real.rpow_nonneg (japBracket_pos η).le (σ - q)
  have hJs := Real.rpow_nonneg (japBracket_pos η).le s
  have hAn : 0 ≤ ∏ i, ‖a i‖ := Finset.prod_nonneg (fun i _ => norm_nonneg _)
  have hP : 0 ≤ ∏ i, ‖coeffHat (gs i) (a i)‖ := Finset.prod_nonneg (fun i _ => norm_nonneg _)
  have hΩs : 0 ≤ ∏ i, peetreOmega (a i) ^ |s| :=
    Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (peetreOmega_pos _).le _)
  have hJp : 0 ≤ ∏ i, japBracket (a i) ^ |σ - q| :=
    Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (japBracket_pos _).le _)
  have hU := norm_nonneg (𝓕 u η)
  have hKs : 0 ≤ (Real.sqrt 2 * 2 ^ q) ^ |s| := by positivity
  -- the kernel product dominates the weight product
  have hker : (∏ i, ‖a i‖) * (∏ i, ‖coeffHat (gs i) (a i)‖) *
        ((∏ i, peetreOmega (a i) ^ |s|) * ∏ i, japBracket (a i) ^ |σ - q|) ≤
      ∏ i, coeffKernel (|σ - q| + |s|) (gs i) (a i) := by
    have e1 : ∏ i, coeffKernel (|σ - q| + |s|) (gs i) (a i) =
        (∏ i, ‖a i‖) * ((∏ i, peetreOmega (a i) ^ (|σ - q| + |s|)) * ∏ i, ‖coeffHat (gs i) (a i)‖) := by
      unfold coeffKernel
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have e2 : (∏ i, peetreOmega (a i) ^ |s|) * ∏ i, japBracket (a i) ^ |σ - q| ≤
        ∏ i, peetreOmega (a i) ^ (|σ - q| + |s|) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod₀ (fun i _ => mul_nonneg (Real.rpow_nonneg (peetreOmega_pos _).le _)
        (Real.rpow_nonneg (japBracket_pos _).le _)) (fun i _ => ?_)
      rw [Real.rpow_add (peetreOmega_pos _)]
      have hj : japBracket (a i) ^ |σ - q| ≤ peetreOmega (a i) ^ |σ - q| := by
        apply Real.rpow_le_rpow (japBracket_pos _).le _ (abs_nonneg _)
        unfold peetreOmega
        have := one_le_japBracket (a i)
        nlinarith [(by rw [Real.one_le_sqrt]; norm_num : (1:ℝ) ≤ Real.sqrt 2)]
      have := mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg (peetreOmega_pos (a i)).le |s|)
      linarith
    rw [e1]
    have := mul_le_mul_of_nonneg_left e2 (mul_nonneg hAn hP)
    calc _ = (∏ i, ‖a i‖) * (∏ i, ‖coeffHat (gs i) (a i)‖) *
          ((∏ i, peetreOmega (a i) ^ |s|) * ∏ i, japBracket (a i) ^ |σ - q|) := rfl
      _ ≤ (∏ i, ‖a i‖) * (∏ i, ‖coeffHat (gs i) (a i)‖) *
          ∏ i, peetreOmega (a i) ^ (|σ - q| + |s|) := this
      _ = _ := by ring
  rw [hnorm]
  have hexp : japBracket η ^ s * japBracket η ^ (σ - q) = japBracket η ^ (s + σ - q) := by
    rw [← Real.rpow_add (japBracket_pos η)]; congr 1; ring
  have key := weighted_aux Ce ((Real.sqrt 2 * 2 ^ q) ^ |s|) (japBracket ξ ^ s) (japBracket η ^ s)
    (japBracket η ^ (σ - q)) (∏ i, peetreOmega (a i) ^ |s|) (∏ i, japBracket (a i) ^ |σ - q|)
    (∏ i, ‖a i‖) (∏ i, ‖coeffHat (gs i) (a i)‖) ‖𝓕 u η‖ ‖fdiffs q a (bracketPow σ) η‖
    (∏ i, coeffKernel (|σ - q| + |s|) (gs i) (a i)) hCe hKs hJs hJη hΩs hJp hAn hP hU (norm_nonneg _)
    h2 h1 hker
  rw [hexp] at key
  exact key


/-- Lower-integral form of the weighted kernel bound. -/
theorem fourierWeight_nestedComm_le (σ : ℝ) (q : ℕ) (s : ℝ) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (gs : Fin q → SchwartzMap (Carrier N) ℝ) (u : TestFunction N)
      (ξ : Carrier N),
      fourierWeightENN s (nestedComm σ q gs u) ξ ≤
        ENNReal.ofReal Cc * ∫⁻ a : Fin q → Carrier N,
          (∏ i, ENNReal.ofReal (coeffKernel (|σ - q| + |s|) (gs i) (a i))) *
            fourierWeightENN (s + (σ - q)) u (ξ - ∑ i, a i) := by
  obtain ⟨Cc, hCc, hb⟩ := weighted_rep_bound (N := N) σ q s
  refine ⟨Cc, hCc, fun gs u ξ => ?_⟩
  have hmeas : Measurable fun a : Fin q → Carrier N => ‖repIntegrand σ q gs u ξ a‖ₑ :=
    (continuous_repIntegrand σ q gs u ξ).enorm.measurable
  calc fourierWeightENN s (nestedComm σ q gs u) ξ
      = ENNReal.ofReal (japBracket ξ ^ s) * ‖∫ a, repIntegrand σ q gs u ξ a‖ₑ := by
        unfold fourierWeightENN; rw [fourier_nestedComm]
    _ ≤ ENNReal.ofReal (japBracket ξ ^ s) * ∫⁻ a, ‖repIntegrand σ q gs u ξ a‖ₑ :=
        by gcongr; exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ a, ENNReal.ofReal (japBracket ξ ^ s) * ‖repIntegrand σ q gs u ξ a‖ₑ :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ a : Fin q → Carrier N, ENNReal.ofReal Cc *
          ((∏ i, ENNReal.ofReal (coeffKernel (|σ - q| + |s|) (gs i) (a i))) *
            fourierWeightENN (s + (σ - q)) u (ξ - ∑ i, a i)) := by
        refine lintegral_mono fun a => ?_
        have h := hb gs u ξ a
        have hk : ∀ i, 0 ≤ coeffKernel (|σ - q| + |s|) (gs i) (a i) := fun i => coeffKernel_nonneg _ _ _
        calc ENNReal.ofReal (japBracket ξ ^ s) * ‖repIntegrand σ q gs u ξ a‖ₑ
            = ENNReal.ofReal (japBracket ξ ^ s * ‖repIntegrand σ q gs u ξ a‖) := by
              rw [ENNReal.ofReal_mul (Real.rpow_nonneg (japBracket_pos _).le _), ofReal_norm]
          _ ≤ ENNReal.ofReal (Cc * (∏ i, coeffKernel (|σ - q| + |s|) (gs i) (a i)) *
                (japBracket (ξ - ∑ i, a i) ^ (s + σ - q) * ‖𝓕 u (ξ - ∑ i, a i)‖)) :=
              ENNReal.ofReal_le_ofReal h
          _ = _ := by
              have e : s + σ - q = s + (σ - q) := by ring
              rw [e, ENNReal.ofReal_mul (mul_nonneg hCc (Finset.prod_nonneg (fun i _ => hk i))),
                ENNReal.ofReal_mul hCc, ENNReal.ofReal_prod_of_nonneg (fun i _ => hk i),
                ENNReal.ofReal_mul (Real.rpow_nonneg (japBracket_pos _).le _), ofReal_norm]
              unfold fourierWeightENN
              ring
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top


/-- The `q`-fold nested commutator of `Λ^σ` with real Schwartz
multipliers has order `σ - q`. -/
theorem hasOrder_nestedComm (σ : ℝ) (q : ℕ) (gs : Fin q → SchwartzMap (Carrier N) ℝ) :
    HasOrder (σ - q) (nestedComm σ q gs) := by
  refine hasOrder_of_iterKernelBound _ _ (fun s => ?_)
  obtain ⟨Cc, hCc, hb⟩ := fourierWeight_nestedComm_le (N := N) σ q s
  set M : ℝ := |σ - q| + |s| with hM
  have hmeas : ∀ i, Measurable fun a : Carrier N => ENNReal.ofReal (coeffKernel M (gs i) a) :=
    fun i => ENNReal.measurable_ofReal.comp (continuous_coeffKernel M (gs i)).measurable
  refine ⟨ENNReal.ofReal Cc, List.ofFn (fun i a => ENNReal.ofReal (coeffKernel M (gs i) a)),
    ENNReal.ofReal_ne_top, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
    exact hmeas i
  · intro k hk
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
    exact ((integrable_coeffKernel M (gs i)).lintegral_lt_top).ne
  · intro u ξ
    refine (hb gs u ξ).trans ?_
    rw [lintegral_pi_eq_iterConv q (fun i a => ENNReal.ofReal (coeffKernel M (gs i) a)) hmeas
      (measurable_fourierWeightENN (s + (σ - q)) u) ξ]


theorem iteratedCommutator_ofFn_multiplier (σ : ℝ) :
    ∀ (n : ℕ) (f : Fin n → SchwartzMap (Carrier N) ℝ),
      iteratedCommutator ((List.ofFn f).map OperatorGenerator.multiplier) (lambdaOperator σ) =
        nestedComm σ n f := by
  intro n
  induction n with
  | zero => intro f; rfl
  | succ n ih =>
    intro f
    rw [List.ofFn_succ, List.map_cons, iteratedCommutator]
    have := ih (fun i => f i.succ)
    rw [this]
    rfl

/-- For real Schwartz multipliers `g₁,…,g_q`, the `q`-fold
commutator `[g₁,[g₂,…[g_q, Λ^σ]…]]` has order `σ - q`. -/
theorem nested_multiplier_order (σ : ℝ) (gs : List (SchwartzMap (Carrier N) ℝ)) :
    HasOrder (σ - gs.length)
      (iteratedCommutator (gs.map OperatorGenerator.multiplier) (lambdaOperator σ)) := by
  have e := iteratedCommutator_ofFn_multiplier σ gs.length (fun i => gs.get i)
  rw [List.ofFn_get] at e
  rw [e]
  exact hasOrder_nestedComm σ gs.length _

end Hormander.B

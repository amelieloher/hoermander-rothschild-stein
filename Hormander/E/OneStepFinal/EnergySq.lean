-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.OneStepFinal.EnergyPairing

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped ComplexConjugate

namespace Hormander.E
open Hormander.B

variable {N : ℕ}

/-- Absorption of the square-root term in the energy inequality. -/
theorem energy_arith {E M n σ τ CA K0 : ℝ} (hE : 0 ≤ E) (hM : 0 ≤ M) (hn0 : 0 ≤ n)
    (_hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (_hCA : 0 ≤ CA) (hK0 : 0 ≤ K0) (hn : n ≤ CA * M)
    {Hn : ℝ} (hH : Hn ≤ M * (σ * Real.sqrt E + τ * n))
    (hEle : E ≤ K0 * (Hn + n ^ 2)) :
    E ≤ (2 * (K0 * (τ * CA + CA ^ 2)) + (K0 * σ) ^ 2) * M ^ 2 := by
  have hs := Real.sqrt_nonneg E
  have hsq := Real.sq_sqrt hE
  have h1 : Hn + n ^ 2 ≤ M * σ * Real.sqrt E + (τ * CA + CA ^ 2) * M ^ 2 := by
    have : τ * n * M ≤ τ * (CA * M) * M := by gcongr
    have h2 : n ^ 2 ≤ (CA * M) ^ 2 := by gcongr
    nlinarith
  have h3 : E ≤ K0 * (M * σ * Real.sqrt E) + K0 * ((τ * CA + CA ^ 2) * M ^ 2) := by
    calc E ≤ K0 * (Hn + n ^ 2) := hEle
      _ ≤ K0 * (M * σ * Real.sqrt E + (τ * CA + CA ^ 2) * M ^ 2) := by gcongr
      _ = _ := by ring
  have h4 : K0 * (M * σ * Real.sqrt E) ≤ (E + (K0 * σ * M) ^ 2) / 2 := by
    nlinarith [sq_nonneg (K0 * σ * M - Real.sqrt E)]
  nlinarith [sq_nonneg M]

theorem exists_abs_bound (f : SchwartzMap (Carrier N) ℝ) : ∃ G : ℝ, ∀ x, |f x| ≤ G :=
  ⟨‖f.toBoundedContinuousFunction‖, fun x => by
    have := f.toBoundedContinuousFunction.norm_coe_le_norm x
    simpa using this⟩


theorem norm_add4_le (a b c d : ℂ) : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  linarith [norm_add_le (a + b + c) d, norm_add_le (a + b) c, norm_add_le a b]

/-- The Hermitian pairing of a test function with `W` is the evaluation at `conj W`. -/
theorem hermitianPairing_eq_eval (ψ W : TestFunction N) :
    hermitianPairing ψ W = (ψ : Tempered N) (conjTest W) := by
  rw [hermitianPairing_eq, testToTempered_apply, bilinearPairing_comm]

theorem vectorField_conjTest' (V : RealSchwartzVectorField N) (W : TestFunction N) :
    vectorFieldOperator V (conjTest W) = conjTest (vectorFieldOperator V W) := by
  have := congrArg (fun T : Operator N => T W) (conjOperator_vectorField V)
  simp only [conjOperator_apply] at this
  rw [← this, conjTest_conjTest]

/-- Energy bound for `W = S_δ T^r u`. -/
theorem energy_sq_bound {k : ℕ} (Vs : Fin (k + 1) → RealSchwartzVectorField N)
    (cs θ η₂ : SchwartzMap (Carrier N) ℝ)
    (hθη : ∀ x ∈ tsupport (θ : Carrier N → ℝ), η₂ x = 1) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : PosScale) (u : Tempered N) (a b : Hormander.A.SobolevSpace N r),
      a.toDistr = cutoffDistr η₂ u →
      b.toDistr = cutoffDistr η₂ (Eop (Hormander.C.diffusionOperator Vs cs) u) →
      ∀ W : TestFunction N, (W : Tempered N) = Eop (energyA θ r d.1 d.2) u →
        ∑ j : Fin k, Hormander.C.normSq (vectorFieldOperator (Vs j.succ) W) ≤
          C * (‖a‖ + ‖b‖) ^ 2 := by
  obtain ⟨CA, hCA0, hCA⟩ := bdd_energyA θ η₂ hθη r
  choose C1 hC10 hC1 using fun j : Fin k => bdd_comm_vf (Vs j.succ) θ η₂ hθη r
  choose C2 hC20 hC2 using fun j : Fin k => bdd_comm2_vf (Vs j.succ) θ η₂ hθη r
  obtain ⟨C3, hC30, hC3⟩ := bdd_comm_vf (Vs 0) θ η₂ hθη r
  obtain ⟨C4, hC40, hC4⟩ := bdd_comm_mult cs θ η₂ hθη r
  choose D hD0 hD using fun j : Fin k => exists_pair_vf_bound (Vs j.succ)
  choose G hG using fun j : Fin (k + 1) => exists_abs_bound (Hormander.C.negDiv (Vs j))
  obtain ⟨Cc, hCc⟩ := exists_abs_bound cs
  set K0 : ℝ := max 2 (G 0 + 2 * Cc + ∑ j : Fin k, G j.succ ^ 2) with hK0
  have hK00 : 0 ≤ K0 := (zero_le_two).trans (le_max_left _ _)
  set σ : ℝ := ∑ j : Fin k, 2 * C1 j with hσ
  set τ : ℝ := CA + ∑ j : Fin k, (2 * C1 j * D j + C2 j) + C3 + C4 with hτ
  have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun j _ => by have := hC10 j; positivity
  have hτ0 : 0 ≤ τ := by
    have : 0 ≤ ∑ j : Fin k, (2 * C1 j * D j + C2 j) :=
      Finset.sum_nonneg fun j _ => by have := hC10 j; have := hD0 j; have := hC20 j; positivity
    positivity
  refine ⟨2 * (K0 * (τ * CA + CA ^ 2)) + (K0 * σ) ^ 2, by positivity, ?_⟩
  intro d u a b ha hb W hW
  set A := energyA θ r d.1 d.2 with hA
  set M := ‖a‖ + ‖b‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have ha_le : ‖a‖ ≤ M := by linarith [norm_nonneg b]
  have hb_le : ‖b‖ ≤ M := by linarith [norm_nonneg a]
  set n := sobolevNorm 0 W with hn_def
  have hn0 : 0 ≤ n := sobolevNorm_nonneg _ _
  have hn : n ≤ CA * M := by
    have h := hCA d u a ha
    rw [← hW] at h
    have := Bdd.test_le h
    calc n ≤ CA * ‖a‖ := this
      _ ≤ CA * M := by gcongr
  set E := ∑ j : Fin k, Hormander.C.normSq (vectorFieldOperator (Vs j.succ) W) with hE
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun j _ => Hormander.C.normSq_nonneg _
  have hen := Hormander.C.complex_energy_estimate Vs cs G Cc (fun j x => hG j x) hCc W
  rw [← sobolevNorm_zero_sq' W] at hen
  have hψ : ((Hormander.C.diffusionOperator Vs cs W : TestFunction N) : Tempered N) =
      Eop ((Hormander.C.diffusionOperator Vs cs).comp A) u := by
    rw [← Eop_test (hct_diffusion Vs cs) W, hW, Eop_comp (hct_diffusion Vs cs) HCT.out]
    rfl
  rw [Eop_diffusion_comp_first Vs cs A u] at hψ
  have hH : hermitianPairing (Hormander.C.diffusionOperator Vs cs W) W =
      Eop A (Eop (Hormander.C.diffusionOperator Vs cs) u) (conjTest W) +
      ∑ j : Fin k, ((2 : ℂ) * Eop (vectorFieldOperator (Vs j.succ))
          (Eop (operatorComm (vectorFieldOperator (Vs j.succ)) A) u) (conjTest W) +
        Eop (operatorComm (operatorComm (vectorFieldOperator (Vs j.succ)) A)
          (vectorFieldOperator (Vs j.succ))) u (conjTest W)) +
      Eop (operatorComm (vectorFieldOperator (Vs 0)) A) u (conjTest W) +
      Eop (operatorComm (realMultiplierOperator cs) A) u (conjTest W) := by
    rw [hermitianPairing_eq_eval, hψ]
    simp
  have hconj : sobolevNorm 0 (conjTest W) = n := sobolevNorm_conjTest 0 W
  have hXconj : ∀ j : Fin k,
      sobolevNorm 0 (vectorFieldOperator (Vs j.succ) (conjTest W)) ≤ Real.sqrt E := by
    intro j
    rw [vectorField_conjTest', sobolevNorm_conjTest, sobolevNorm_zero_eq_sqrt]
    apply Real.sqrt_le_sqrt
    exact Finset.single_le_sum (f := fun j : Fin k =>
      Hormander.C.normSq (vectorFieldOperator (Vs j.succ) W))
      (fun j _ => Hormander.C.normSq_nonneg _) (Finset.mem_univ j)
  have t1 : ‖Eop A (Eop (Hormander.C.diffusionOperator Vs cs) u) (conjTest W)‖ ≤ CA * M * n := by
    have h := hCA d (Eop (Hormander.C.diffusionOperator Vs cs) u) b hb
    calc _ ≤ CA * ‖b‖ * sobolevNorm 0 (conjTest W) := h.pairing _
      _ ≤ CA * M * n := by rw [hconj]; gcongr
  have t2 : ∀ j : Fin k, ‖Eop (vectorFieldOperator (Vs j.succ))
      (Eop (operatorComm (vectorFieldOperator (Vs j.succ)) A) u) (conjTest W)‖ ≤
        C1 j * M * (Real.sqrt E + D j * n) := by
    intro j
    have h := hC1 j d u a ha
    calc _ ≤ (C1 j * ‖a‖) * (sobolevNorm 0 (vectorFieldOperator (Vs j.succ) (conjTest W)) +
          D j * sobolevNorm 0 (conjTest W)) := hD j _ _ _ h
      _ ≤ C1 j * M * (Real.sqrt E + D j * n) := by
        rw [hconj]
        have hS0 : 0 ≤ sobolevNorm 0 (vectorFieldOperator (Vs j.succ) (conjTest W)) + D j * n :=
          add_nonneg (sobolevNorm_nonneg _ _) (mul_nonneg (hD0 j) hn0)
        exact mul_le_mul (mul_le_mul_of_nonneg_left ha_le (hC10 j))
          (add_le_add (hXconj j) le_rfl) hS0 (mul_nonneg (hC10 j) hM0)
  have t3 : ∀ j : Fin k, ‖Eop (operatorComm (operatorComm (vectorFieldOperator (Vs j.succ)) A)
      (vectorFieldOperator (Vs j.succ))) u (conjTest W)‖ ≤ C2 j * M * n := by
    intro j
    have h := hC2 j d u a ha
    calc _ ≤ C2 j * ‖a‖ * sobolevNorm 0 (conjTest W) := h.pairing _
      _ ≤ C2 j * M * n := by rw [hconj]; have := hC20 j; gcongr
  have t4 : ‖Eop (operatorComm (vectorFieldOperator (Vs 0)) A) u (conjTest W)‖ ≤ C3 * M * n := by
    have h := hC3 d u a ha
    calc _ ≤ C3 * ‖a‖ * sobolevNorm 0 (conjTest W) := h.pairing _
      _ ≤ C3 * M * n := by rw [hconj]; gcongr
  have t5 : ‖Eop (operatorComm (realMultiplierOperator cs) A) u (conjTest W)‖ ≤ C4 * M * n := by
    have h := hC4 d u a ha
    calc _ ≤ C4 * ‖a‖ * sobolevNorm 0 (conjTest W) := h.pairing _
      _ ≤ C4 * M * n := by rw [hconj]; gcongr
  have hsum : ∑ j : Fin k, (2 * (C1 j * M * (Real.sqrt E + D j * n)) + C2 j * M * n) =
      M * (σ * Real.sqrt E + (∑ j : Fin k, (2 * C1 j * D j + C2 j)) * n) := by
    simp only [σ, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hHn : ‖hermitianPairing (Hormander.C.diffusionOperator Vs cs W) W‖ ≤
      M * (σ * Real.sqrt E + τ * n) := by
    rw [hH]
    refine norm_add4_le _ _ _ _ |>.trans ?_
    have hS : ‖∑ j : Fin k, ((2 : ℂ) * Eop (vectorFieldOperator (Vs j.succ))
          (Eop (operatorComm (vectorFieldOperator (Vs j.succ)) A) u) (conjTest W) +
        Eop (operatorComm (operatorComm (vectorFieldOperator (Vs j.succ)) A)
          (vectorFieldOperator (Vs j.succ))) u (conjTest W))‖ ≤
        ∑ j : Fin k, (2 * (C1 j * M * (Real.sqrt E + D j * n)) + C2 j * M * n) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      refine (norm_add_le _ _).trans (add_le_add ?_ (t3 j))
      rw [norm_mul]
      simp only [Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left (t2 j) (by norm_num)
    calc _ ≤ CA * M * n + ∑ j : Fin k, (2 * (C1 j * M * (Real.sqrt E + D j * n)) + C2 j * M * n)
        + C3 * M * n + C4 * M * n := by linarith [t1, hS, t4, t5]
      _ = M * (σ * Real.sqrt E + τ * n) := by
        rw [hsum]; simp only [τ]; ring
  have hEle : E ≤ K0 * (‖hermitianPairing (Hormander.C.diffusionOperator Vs cs W) W‖ + n ^ 2) :=
    hen
  have := energy_arith hE0 hM0 hn0 hσ0 hτ0 hCA0 hK00 hn hHn
    (hEle.trans (by gcongr))
  exact this

end Hormander.E

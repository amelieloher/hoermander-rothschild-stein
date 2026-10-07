-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Nested.SymbolDerivatives
public import Hormander.B.Nested.FiniteDifference

@[expose] public section

noncomputable section

namespace Hormander.B

section e22
variable {N : ℕ}

theorem peetreOmega_sum_le (q : ℕ) :
    ∀ (t : Fin q → ℝ), (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) → ∀ (h : Fin q → Carrier N),
      peetreOmega (∑ i, t i • h i) ≤ Real.sqrt 2 * 2 ^ q * ∏ i, peetreOmega (h i) := by
  induction q with
  | zero =>
    intro t _ h
    simp [peetreOmega, japBracket, bracketSq]
  | succ q ih =>
    intro t ht h
    rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
    have h1 := ih (fun i => t i.succ) (fun i => ht i.succ) (fun i => h i.succ)
    have h2 : peetreOmega (t 0 • h 0) ≤ peetreOmega (h 0) := by
      apply peetreOmega_mono
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ht 0).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (ht 0).2
    have h3 := peetreOmega_add_le (t 0 • h 0) (∑ i : Fin q, t i.succ • h i.succ)
    have hp0 := peetreOmega_pos (t 0 • h 0)
    have hpr : 0 < ∏ i : Fin q, peetreOmega (h i.succ) :=
      Finset.prod_pos (fun i _ => peetreOmega_pos _)
    calc peetreOmega (t 0 • h 0 + ∑ i : Fin q, t i.succ • h i.succ)
        ≤ 2 * (peetreOmega (t 0 • h 0) * peetreOmega (∑ i : Fin q, t i.succ • h i.succ)) := h3
      _ ≤ 2 * (peetreOmega (h 0) * (Real.sqrt 2 * 2 ^ q * ∏ i : Fin q, peetreOmega (h i.succ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul h2 h1 (peetreOmega_pos _).le (peetreOmega_pos _).le) (by norm_num)
      _ = _ := by ring

/-- The `q`-fold finite difference of `⟨·⟩^σ` obeys
`|Δ_{h₁}⋯Δ_{h_q} F (η)| ≤ C (∏ |h_i|) ⟨η⟩^{σ-q} ∏ ⟨h_i⟩^{|σ-q|}` (product Peetre weights). -/
theorem finite_difference_bound (q : ℕ) (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (η : Carrier N) (h : Fin q → Carrier N),
      ‖fdiffs q h (bracketPow σ) η‖ ≤
        C * ((∏ i, ‖h i‖) * japBracket η ^ (σ - q) * ∏ i, japBracket (h i) ^ |σ - q|) := by
  obtain ⟨C₁, hC₁, hD⟩ := norm_iteratedFDeriv_bracketPow_le (E := Carrier N) q σ
  set p : ℝ := σ - q with hp
  set K : ℝ := (Real.sqrt 2 * 2 ^ q) ^ |p| with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨C₁ * K * (Real.sqrt 2) ^ ((q : ℝ) * |p|), by positivity, fun η h => ?_⟩
  set M : ℝ := C₁ * japBracket η ^ p * (K * ∏ i, peetreOmega (h i) ^ |p|) with hM
  have hbound := norm_fdiffs_le q ((contDiff_bracketPow (E := Carrier N) σ).of_le (by exact_mod_cast le_top)) η h M (fun t ht => by
    refine (hD _).trans ?_
    set s : Carrier N := ∑ i, t i • h i with hs
    have h1 := peetre_jap (η + s) η p
    rw [add_sub_cancel_left] at h1
    have h2 := peetreOmega_sum_le q t ht h
    have h3 : peetreOmega s ^ |p| ≤ K * ∏ i, peetreOmega (h i) ^ |p| := by
      calc peetreOmega s ^ |p| ≤ (Real.sqrt 2 * 2 ^ q * ∏ i, peetreOmega (h i)) ^ |p| :=
            Real.rpow_le_rpow (peetreOmega_pos _).le h2 (abs_nonneg p)
        _ = K * ∏ i, peetreOmega (h i) ^ |p| := by
            rw [Real.mul_rpow (by positivity) (Finset.prod_nonneg (fun i _ => (peetreOmega_pos _).le)),
              Real.finsetProd_rpow _ _ (fun i _ => (peetreOmega_pos _).le)]
    calc C₁ * japBracket (η + s) ^ p ≤ C₁ * (japBracket η ^ p * peetreOmega s ^ |p|) :=
          mul_le_mul_of_nonneg_left h1 hC₁
      _ ≤ C₁ * (japBracket η ^ p * (K * ∏ i, peetreOmega (h i) ^ |p|)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3
            (Real.rpow_nonneg (japBracket_pos η).le p)) hC₁
      _ = M := by rw [hM]; ring)
  refine hbound.trans ?_
  have hω : ∏ i, peetreOmega (h i) ^ |p| = (Real.sqrt 2 ^ |p|) ^ q * ∏ i, japBracket (h i) ^ |p| := by
    have : ∀ i, peetreOmega (h i) ^ |p| = Real.sqrt 2 ^ |p| * japBracket (h i) ^ |p| := fun i => by
      unfold peetreOmega
      rw [Real.mul_rpow (Real.sqrt_nonneg 2) (japBracket_pos _).le]
    rw [Finset.prod_congr rfl (fun i _ => this i), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hc : (Real.sqrt 2) ^ ((q : ℝ) * |p|) = (Real.sqrt 2 ^ |p|) ^ q := by
    rw [mul_comm, Real.rpow_mul (Real.sqrt_nonneg 2), Real.rpow_natCast]
  rw [hM, hω, hc]
  apply le_of_eq
  ring

end e22

end Hormander.B

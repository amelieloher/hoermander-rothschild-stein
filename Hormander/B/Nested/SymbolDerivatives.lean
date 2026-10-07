-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.TaylorWeights
public import Hormander.B.Fractional.Peetre
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace ContDiff

namespace Hormander.B


section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The bracket power `⟨z⟩^σ` as a function on `E`. -/
def bracketPow (σ : ℝ) (z : E) : ℝ := japBracket z ^ σ

omit [InnerProductSpace ℝ E] in
theorem bracketPow_eq_radialWeight (σ : ℝ) (z : E) : bracketPow σ z = radialWeight z σ := by
  unfold bracketPow radialWeight
  exact japBracket_rpow z σ

theorem contDiff_bracketPow (σ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (bracketPow (E := E) σ) := by
  have : bracketPow (E := E) σ = fun z => radialWeight z σ := funext (bracketPow_eq_radialWeight σ)
  rw [this]
  exact contDiff_radialWeight σ

theorem hasFDerivAt_bracketPow (σ : ℝ) (z : E) :
    HasFDerivAt (bracketPow σ) ((σ * japBracket z ^ (σ - 2)) • innerSL ℝ z) z := by
  have h1 : HasFDerivAt (fun x : E => bracketSq x) ((2 : ℕ) • innerSL ℝ z) z := by
    have := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add 1
    simpa [bracketSq] using this
  have hpos : bracketSq z ≠ 0 := (bracketSq_pos' z).ne'
  have h2 := h1.rpow_const (p := σ / 2) (Or.inl hpos)
  have e : bracketPow σ = fun x : E => bracketSq x ^ (σ / 2) := by
    funext x; exact japBracket_rpow x σ
  rw [e]
  convert h2 using 1
  rw [japBracket_rpow, show σ / 2 - 1 = (σ - 2) / 2 by ring]
  ext v
  simp
  ring


theorem fderiv_bracketPow (σ : ℝ) :
    fderiv ℝ (bracketPow (E := E) σ) = fun z => (σ * bracketPow (σ - 2) z) • innerSL ℝ z := by
  funext z
  exact (hasFDerivAt_bracketPow σ z).fderiv

/-- The inner product map `z ↦ ⟪z, ·⟫` as a real continuous linear map. -/
def innerCLM (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ

theorem fderiv_innerCLM (z : E) : fderiv ℝ (fun y : E => innerCLM E y) z = innerCLM E :=
  (innerCLM E).fderiv

/-- Derivatives of the inner product map `z ↦ ⟪z, ·⟫`. -/
theorem norm_iteratedFDeriv_innerCLM_le (k : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ k (fun y : E => innerCLM E y) z‖ ≤
      if k = 0 then japBracket z else if k = 1 then 1 else 0 := by
  rcases k with _ | _ | k
  · simp only [norm_iteratedFDeriv_zero, ite_true]
    calc ‖innerCLM E z‖ ≤ ‖z‖ := (innerSL_apply_norm ℝ z).le
      _ ≤ japBracket z := norm_le_japBracket z
  · have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun y : E => innerCLM E y) (x := z) (n := 0)
    rw [zero_add] at h
    rw [← h, norm_iteratedFDeriv_zero, fderiv_innerCLM]
    simp only [zero_add, one_ne_zero, ite_false, ite_true]
    exact norm_innerSL_le ℝ
  · have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun y : E => innerCLM E y) (x := z) (n := k + 1)
    rw [show k + 1 + 1 = k + 2 from rfl] at h
    rw [← h]
    have : fderiv ℝ (fun y : E => innerCLM E y) = fun _ => innerCLM E := funext fderiv_innerCLM
    rw [this, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]
    simp


/-- Symbol estimates: `‖D^q ⟨z⟩^σ‖ ≤ C_{q,σ} ⟨z⟩^{σ-q}`. -/
theorem norm_iteratedFDeriv_bracketPow_le (q : ℕ) :
    ∀ σ : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E,
      ‖iteratedFDeriv ℝ q (bracketPow σ) z‖ ≤ C * japBracket z ^ (σ - q) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro σ
    rcases q with _ | q
    · refine ⟨1, zero_le_one, fun z => ?_⟩
      rw [norm_iteratedFDeriv_zero]
      simp [bracketPow, abs_of_nonneg (Real.rpow_nonneg (japBracket_pos z).le σ)]
    · have hall : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (i ≤ q → ∀ z : E,
          ‖iteratedFDeriv ℝ i (bracketPow (σ - 2)) z‖ ≤ C * japBracket z ^ (σ - 2 - i)) := by
        intro i
        by_cases hi : i ≤ q
        · obtain ⟨C, hC, h⟩ := ih i (Nat.lt_succ_of_le hi) (σ - 2)
          exact ⟨C, hC, fun _ => h⟩
        · exact ⟨0, le_rfl, fun h => absurd h hi⟩
      choose Cf hCf0 hCf using hall
      refine ⟨∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * (|σ| * Cf i),
        Finset.sum_nonneg (fun i _ => by have := hCf0 i; positivity), fun z => ?_⟩
      have hsm : ContDiff ℝ (⊤ : ℕ∞) (bracketPow (E := E) σ) := contDiff_bracketPow σ
      rw [← norm_iteratedFDeriv_fderiv, fderiv_bracketPow]
      have hfa : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => σ * bracketPow (σ - 2) y) :=
        contDiff_const.mul (contDiff_bracketPow (σ - 2))
      have hga : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => innerCLM E y) := (innerCLM E).contDiff
      have hmain := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (𝕜' := ℝ) hfa hga z
        (n := q) (N := ((⊤ : ℕ∞) : ℕ∞ω)) (by exact_mod_cast le_top)
      refine hmain.trans ?_
      have hjp := japBracket_pos z
      have hterm : ∀ i ∈ Finset.range (q + 1),
          (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => σ * bracketPow (σ - 2) y) z‖ *
              ‖iteratedFDeriv ℝ (q - i) (fun y : E => innerCLM E y) z‖ ≤
            (q.choose i : ℝ) * (|σ| * Cf i) * japBracket z ^ (σ - ((q + 1 : ℕ) : ℝ)) := by
        intro i hi
        have hiq : i ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hfi : ‖iteratedFDeriv ℝ i (fun y : E => σ * bracketPow (σ - 2) y) z‖ ≤
            |σ| * (Cf i * japBracket z ^ (σ - 2 - i)) := by
          have : (fun y : E => σ * bracketPow (σ - 2) y) = σ • bracketPow (σ - 2) := rfl
          rw [this, iteratedFDeriv_const_smul_apply
            ((contDiff_bracketPow (σ - 2)).contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul,
            Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hCf i hiq z) (abs_nonneg σ)
        have hgi := norm_iteratedFDeriv_innerCLM_le (q - i) z
        have hCi := hCf0 i
        have hpow : 0 < japBracket z := hjp
        have hRHS : 0 ≤ (q.choose i : ℝ) * (|σ| * Cf i) * japBracket z ^ (σ - ((q + 1 : ℕ) : ℝ)) := by
          positivity
        have hchoose : (0 : ℝ) ≤ q.choose i := Nat.cast_nonneg _
        have hfi0 : 0 ≤ ‖iteratedFDeriv ℝ i (fun y : E => σ * bracketPow (σ - 2) y) z‖ := norm_nonneg _
        by_cases h0 : q - i = 0
        · have hiq' : i = q := by omega
          subst hiq'
          simp only [h0, ite_true] at hgi
          rw [h0] at hgi
          rw [Nat.choose_self, h0, Nat.cast_one]
          rw [Nat.choose_self, Nat.cast_one] at hRHS
          have e : japBracket z ^ (σ - 2 - (i : ℝ)) * japBracket z = japBracket z ^ (σ - ((i + 1 : ℕ) : ℝ)) := by
            rw [← Real.rpow_add_one hjp.ne']
            congr 1
            push_cast
            ring
          calc (1 : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => σ * bracketPow (σ - 2) y) z‖ *
                ‖iteratedFDeriv ℝ 0 (fun y : E => innerCLM E y) z‖
              ≤ 1 * (|σ| * (Cf i * japBracket z ^ (σ - 2 - i))) * japBracket z := by
                gcongr
            _ = _ := by
                rw [← e]; ring
        · by_cases h1 : q - i = 1
          · rw [h1] at hgi
            simp only [one_ne_zero, ite_false, ite_true] at hgi
            have hgi' : ‖iteratedFDeriv ℝ 1 (fun y : E => innerCLM E y) z‖ ≤ 1 := by simpa using hgi
            have e : σ - 2 - (i : ℝ) = σ - ((q + 1 : ℕ) : ℝ) := by
              have : (i : ℝ) + 1 = q := by exact_mod_cast (by omega : i + 1 = q)
              push_cast; linarith
            rw [h1]
            calc (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => σ * bracketPow (σ - 2) y) z‖ *
                  ‖iteratedFDeriv ℝ 1 (fun y : E => innerCLM E y) z‖
                ≤ (q.choose i : ℝ) * (|σ| * (Cf i * japBracket z ^ (σ - 2 - i))) * 1 := by
                  gcongr
              _ = _ := by rw [e]; ring
          · simp only [h0, h1, ite_false] at hgi
            have : ‖iteratedFDeriv ℝ (q - i) (fun y : E => innerCLM E y) z‖ = 0 :=
              le_antisymm hgi (norm_nonneg _)
            rw [this, mul_zero]
            exact hRHS
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul]

end

end Hormander.B

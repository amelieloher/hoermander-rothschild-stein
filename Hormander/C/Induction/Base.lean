-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Induction.L2

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped ComplexConjugate
namespace Hormander.C
open Hormander.B
variable {N : ℕ}

theorem exists_sup_bound (g : SchwartzMap (Carrier N) ℝ) : ∃ G : ℝ, 0 ≤ G ∧ ∀ x, |g x| ≤ G :=
  ⟨SchwartzMap.seminorm ℝ 0 0 g, by positivity, fun x => by
    simpa using SchwartzMap.norm_le_seminorm ℝ g x⟩

/-- Young: `‖(a,b)‖ ≤ ½‖a‖² + ½‖b‖²`. -/
theorem norm_H_le_young (u v : TestFunction N) :
    ‖hermitianPairing u v‖ ≤ (1 / 2) * normSq u + (1 / 2) * normSq v := by
  refine (norm_H_le u v).trans ?_
  rw [← sobolevNorm_zero_sq, ← sobolevNorm_zero_sq]
  nlinarith [sq_nonneg (sobolevNorm 0 u - sobolevNorm 0 v)]

/-- The energy estimate in the form `∑ⱼ ‖Xⱼφ‖₂² ≤ C (‖Lφ‖₂² + ‖φ‖₂²)`. -/
theorem energy_bound {k : ℕ} (X : Fin (k + 1) → RealSchwartzVectorField N)
    (c : SchwartzMap (Carrier N) ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : TestFunction N,
      ∑ j : Fin k, normSq (vectorFieldOperator (X j.succ) φ) ≤
        C * (normSq (diffusionOperator X c φ) + normSq φ) := by
  have hG : ∀ j : Fin (k + 1), ∃ G : ℝ, 0 ≤ G ∧ ∀ x, |negDiv (X j) x| ≤ G :=
    fun j => exists_sup_bound _
  choose G hG0 hG using hG
  obtain ⟨Cc, hCc0, hc⟩ := exists_sup_bound c
  set C0 := max 2 (G 0 + 2 * Cc + ∑ j : Fin k, G j.succ ^ 2) with hC0
  have hC0pos : 0 < C0 := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨3 / 2 * C0, by positivity, fun φ => ?_⟩
  have h6 := complex_energy_estimate X c G Cc hG hc φ
  have hy := norm_H_le_young (diffusionOperator X c φ) φ
  have hn := normSq_nonneg φ
  have ha := normSq_nonneg (diffusionOperator X c φ)
  calc _ ≤ C0 * (‖hermitianPairing (diffusionOperator X c φ) φ‖ + normSq φ) := h6
    _ ≤ C0 * ((1 / 2) * normSq (diffusionOperator X c φ) + (1 / 2) * normSq φ + normSq φ) :=
        mul_le_mul_of_nonneg_left (by linarith) hC0pos.le
    _ ≤ 3 / 2 * C0 * (normSq (diffusionOperator X c φ) + normSq φ) := by nlinarith

/-- For `j ≥ 1` and `0 < α ≤ 1/2`:
`‖X_j u‖²_{H^{α-1}} ≤ C (‖Lu‖₂² + ‖u‖₂²)`. -/
theorem base_horizontal {k : ℕ} (X : Fin (k + 1) → RealSchwartzVectorField N)
    (c : SchwartzMap (Carrier N) ℝ) {α : ℝ} (hα : α ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin k) (u : TestFunction N),
      sobolevNorm (α - 1) (vectorFieldOperator (X j.succ) u) ^ 2 ≤
        C * (normSq (diffusionOperator X c u) + normSq u) := by
  obtain ⟨C, hC, hE⟩ := energy_bound X c
  refine ⟨C, hC, fun j u => ?_⟩
  have h1 : sobolevNorm (α - 1) (vectorFieldOperator (X j.succ) u) ≤
      sobolevNorm 0 (vectorFieldOperator (X j.succ) u) := sobolevNorm_mono (by linarith) _
  have h0 : 0 ≤ sobolevNorm (α - 1) (vectorFieldOperator (X j.succ) u) := sobolevNorm_nonneg _ _
  have h2 : sobolevNorm (α - 1) (vectorFieldOperator (X j.succ) u) ^ 2 ≤
      normSq (vectorFieldOperator (X j.succ) u) := by
    rw [← sobolevNorm_zero_sq]; exact pow_le_pow_left₀ h0 h1 2
  refine h2.trans ((Finset.single_le_sum (f := fun j : Fin k => normSq (vectorFieldOperator (X j.succ) u))
    (fun i _ => normSq_nonneg _) (Finset.mem_univ j)).trans (hE u))

end Hormander.C

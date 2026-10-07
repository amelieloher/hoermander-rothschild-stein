-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Induction.DriftA

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory SchwartzMap
open scoped ComplexConjugate
namespace Hormander.C
open Hormander.B
variable {N k : ℕ} {D : DriftData N k} {T : Operator N}

/-- in raw form: `∑ ‖Xⱼφ‖² ≤ C (|(Lφ,φ)| + ‖φ‖²)`. -/
theorem energy_raw {k : ℕ} (X : Fin (k + 1) → RealSchwartzVectorField N)
    (c : SchwartzMap (Carrier N) ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : TestFunction N,
      ∑ j : Fin k, normSq (vectorFieldOperator (X j.succ) φ) ≤
        C * (‖hermitianPairing (diffusionOperator X c φ) φ‖ + normSq φ) := by
  have hG : ∀ j : Fin (k + 1), ∃ G : ℝ, 0 ≤ G ∧ ∀ x, |negDiv (X j) x| ≤ G :=
    fun j => exists_sup_bound _
  choose G hG0 hG using hG
  obtain ⟨Cc, hCc0, hc⟩ := exists_sup_bound c
  refine ⟨max 2 (G 0 + 2 * Cc + ∑ j : Fin k, G j.succ ^ 2), lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    fun φ => complex_energy_estimate X c G Cc hG hc φ⟩

theorem sqrt_bound {x K s : ℝ} (_hx : 0 ≤ x) (hK : 0 ≤ K) (hs : 0 ≤ s) (h : x ^ 2 ≤ K * s ^ 2) :
    x ≤ Real.sqrt K * s := by
  have : x ^ 2 ≤ (Real.sqrt K * s) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hK]; exact h
  exact le_of_sq_le_sq this (by positivity)
  
namespace DriftHyp
variable (h : DriftHyp D T)
include h

theorem termP {Ts : Operator N} (hTsc : OperatorClass (2 * D.α - 1) Ts) (i : Fin k) :
    SBound D (fun u => hermitianPairing (D.V i.succ (Ts (D.W u))) (D.V i.succ u)) := by
  obtain ⟨C0, hC0, hE⟩ := energy_raw D.X D.c
  have hR : OperatorClass (2 * D.α) (Ts.comp D.W) := by
    have := h.F.comp_mem _ 1 _ _ hTsc (h.F.vectorField_mem D.Y)
    have e : 2 * D.α - 1 + 1 = 2 * D.α := by ring
    rw [e] at this
    exact this
  obtain ⟨Rj, R0, hRj, hR0, hdec⟩ := commutator_left_decomposition_of_B10 h.F D.X D.c hR
  have hW4 : SLe D (fun u => sobolevNorm (2 * D.α + (2 * D.α - 1)) (D.W u)) := by
    have : 2 * D.α + (2 * D.α - 1) = 4 * D.α - 1 := by ring
    rw [this]; exact h.sW4
  have hφ2 : SLe D (fun u => sobolevNorm (2 * D.α) (Ts (D.W u))) :=
    SLe.of_order hTsc.hasOrder' (2 * D.α) hW4
  have hφ0 : SLe D (fun u => sobolevNorm 0 (Ts (D.W u))) :=
    SLe.of_order hTsc.hasOrder' 0 (by simpa using h.sWτ)
  -- the pairing `(L φ, φ)`
  have hLφ : ∀ u, D.L (Ts (D.W u)) = (Ts.comp D.W) (D.L u) +
      ((∑ j : Fin k, (Rj j) (D.V j.succ u)) + R0 u) := fun u => by
    have := LinearMap.congr_fun hdec u
    simp only [operatorComm, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.sum_apply] at this
    have this' : D.L (Ts (D.W u)) - Ts (D.W (D.L u)) =
        ∑ j : Fin k, (Rj j) (D.V j.succ u) + R0 u := this
    rw [sub_eq_iff_eq_add] at this'
    rw [this']
    change _ = Ts (D.W (D.L u)) + _
    abel
  have hH : SBound D (fun u => hermitianPairing (D.L (Ts (D.W u))) (Ts (D.W u))) := by
    have e : ∀ u, hermitianPairing (D.L (Ts (D.W u))) (Ts (D.W u)) =
        hermitianPairing ((Ts.comp D.W) (D.L u)) (Ts (D.W u)) +
        (∑ j : Fin k, hermitianPairing ((Rj j) (D.V j.succ u)) (Ts (D.W u)) +
          hermitianPairing (R0 u) (Ts (D.W u))) := fun u => by
      rw [hLφ u, H_add_left, H_add_left, H_sum_left]
    simp_rw [e]
    refine SBound.add ?_ (SBound.add (SBound.sum fun j => ?_) ?_)
    · exact SBound.left' h.F hR (2 * D.α) 0 (by ring) h.sLu hφ2 (A := fun u => D.L u)
        (B := fun u => Ts (D.W u))
    · exact SBound.left' h.F (hRj j) (2 * D.α) 0 (by ring) (h.sV j) hφ2
        (A := fun u => D.V j.succ u) (B := fun u => Ts (D.W u))
    · exact SBound.left' h.F hR0 (2 * D.α) 0 (by ring) h.sn hφ2
        (A := fun u => u) (B := fun u => Ts (D.W u))
  obtain ⟨K1, hK1, hH'⟩ := hH
  obtain ⟨Kφ, hKφ, hφ0'⟩ := hφ0
  have hK2 : 0 ≤ C0 * (K1 + Kφ ^ 2) := by positivity
  refine SBound.of_le (K := Real.sqrt (C0 * (K1 + Kφ ^ 2))) (Real.sqrt_nonneg _) fun u => ?_
  have hSn := D.S_nonneg u
  have h1 : normSq (D.V i.succ (Ts (D.W u))) ≤ C0 * (K1 + Kφ ^ 2) * D.S u ^ 2 := by
    refine (Finset.single_le_sum (f := fun j : Fin k => normSq (vectorFieldOperator (D.X j.succ) (Ts (D.W u))))
      (fun j _ => normSq_nonneg _) (Finset.mem_univ i)).trans ((hE _).trans ?_)
    have a1 := hH' u
    have a2 : normSq (Ts (D.W u)) ≤ Kφ ^ 2 * D.S u ^ 2 := by
      rw [← sobolevNorm_zero_sq, ← mul_pow]
      exact pow_le_pow_left₀ (sobolevNorm_nonneg _ _) (hφ0' u) 2
    change C0 * (‖hermitianPairing (D.L (Ts (D.W u))) (Ts (D.W u))‖ + normSq (Ts (D.W u))) ≤ _
    nlinarith
  have h2 : sobolevNorm 0 (D.V i.succ (Ts (D.W u))) ≤ Real.sqrt (C0 * (K1 + Kφ ^ 2)) * D.S u := by
    refine sqrt_bound (sobolevNorm_nonneg _ _) hK2 hSn ?_
    rw [sobolevNorm_zero_sq]; exact h1
  calc ‖hermitianPairing (D.V i.succ (Ts (D.W u))) (D.V i.succ u)‖
      ≤ sobolevNorm 0 (D.V i.succ (Ts (D.W u))) * sobolevNorm 0 (D.V i.succ u) := norm_H_le _ _
    _ ≤ (Real.sqrt (C0 * (K1 + Kφ ^ 2)) * D.S u) * D.S u :=
        mul_le_mul h2 (D.e_le_S i u) (sobolevNorm_nonneg _ _) (by positivity)
    _ = _ := by ring

end DriftHyp
end Hormander.C

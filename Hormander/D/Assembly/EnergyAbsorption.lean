-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.D.Assembly.CommutatorStep
public import Hormander.D.Assembly.EnergyPairing
public import Hormander.D.EnergyAlgebra
public import Hormander.C.Induction.L2
public import Hormander.C.Energy.Estimate

@[expose] public section

noncomputable section

namespace Hormander.D

open Hormander.B

/-- The full-sum energy estimate for a complex Schwartz function. -/
theorem energy_estimate_l2 {N k : ℕ} (V : Fin (k + 1) → RealSchwartzVectorField N)
    (cS : SchwartzMap (Carrier N) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : TestFunction N,
      ∑ j : Fin k, sobolevNorm 0 (vectorFieldOperator (V j.succ) φ) ^ 2 ≤
        C * (‖hermitianPairing (Hormander.C.diffusionOperator V cS φ) φ‖ +
          sobolevNorm 0 φ ^ 2) := by
  let G : Fin (k + 1) → ℝ := fun j =>
    SchwartzMap.seminorm ℝ 0 0 (Hormander.C.negDiv (V j))
  have hG : ∀ j x, |Hormander.C.negDiv (V j) x| ≤ G j := fun j x => by
    simpa only [Real.norm_eq_abs] using
      SchwartzMap.norm_le_seminorm ℝ (Hormander.C.negDiv (V j)) x
  have hc : ∀ x, |cS x| ≤ SchwartzMap.seminorm ℝ 0 0 cS := fun x => by
    simpa only [Real.norm_eq_abs] using SchwartzMap.norm_le_seminorm ℝ cS x
  refine ⟨max 2 (G 0 + 2 * SchwartzMap.seminorm ℝ 0 0 cS + ∑ j : Fin k, G j.succ ^ 2),
    (zero_le_two).trans (le_max_left _ _), fun φ => ?_⟩
  have h := Hormander.C.complex_energy_estimate V cS G (SchwartzMap.seminorm ℝ 0 0 cS) hG hc φ
  simpa only [Hormander.C.sobolevNorm_zero_sq] using h


/-- Cauchy–Schwarz for a finite sum of nonnegative reals against its square-sum. -/
private theorem sum_le_sqrt_card_mul_sqrt_sum_sq {k : ℕ} (z : Fin k → ℝ) (hz : ∀ j, 0 ≤ z j) :
    ∑ j : Fin k, z j ≤ Real.sqrt (k : ℝ) * Real.sqrt (∑ j : Fin k, z j ^ 2) := by
  have hsum_nonneg : 0 ≤ ∑ j : Fin k, z j := Finset.sum_nonneg fun j _ => hz j
  have hcs : (∑ j : Fin k, z j) ^ 2 ≤ (k : ℝ) * ∑ j : Fin k, z j ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin k => (1 : ℝ)) z
  have henergy_nonneg : 0 ≤ ∑ j : Fin k, z j ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsq : (∑ j : Fin k, z j) ^ 2 ≤
      (Real.sqrt (k : ℝ) * Real.sqrt (∑ j : Fin k, z j ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg k), Real.sq_sqrt henergy_nonneg]
    exact hcs
  exact (sq_le_sq₀ hsum_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp hsq

/-- The commutator energy bound, given the pairing estimate as a hypothesis. -/
theorem commutator_energy_le_of_pairing {N k : ℕ}
    (V : Fin (k + 1) → RealSchwartzVectorField N)
    (cS : SchwartzMap (Carrier N) ℝ) (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (σ : ℝ)
    (hη₁η' : cutoffPrecedes (η₁ : Carrier N → ℝ) (η' : Carrier N → ℝ))
    (hη'η₂ : cutoffPrecedes (η' : Carrier N → ℝ) (η₂ : Carrier N → ℝ))
    (hpair : ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin k) (u : TestFunction N),
      ‖hermitianPairing (Hormander.C.diffusionOperator V cS
          (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ) u))
        (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ) u)‖ ≤
      C * (sobolevNorm σ (realMultiplierOperator η₂ (Hormander.C.diffusionOperator V cS u)) *
            sobolevNorm σ (realMultiplierOperator η₂ u) +
          sobolevNorm σ (realMultiplierOperator η₂ u) *
            ∑ j : Fin k, sobolevNorm 0 (vectorFieldOperator (V j.succ)
              (operatorComm (vectorFieldOperator (V i.succ))
                (localizedBesselOperator η₁ η' σ) u)) +
          sobolevNorm σ (realMultiplierOperator η₂ u) ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin k) (u : TestFunction N),
      ∑ j : Fin k, sobolevNorm 0 (vectorFieldOperator (V j.succ)
          (operatorComm (vectorFieldOperator (V i.succ))
            (localizedBesselOperator η₁ η' σ) u)) ^ 2 ≤
        C * (sobolevNorm σ (realMultiplierOperator η₂ (Hormander.C.diffusionOperator V cS u)) ^ 2 +
          sobolevNorm σ (realMultiplierOperator η₂ u) ^ 2) := by
  obtain ⟨C8, hC80, h8⟩ := energy_estimate_l2 V cS
  obtain ⟨Cp, hCp0, hp⟩ := hpair
  obtain ⟨C9, h9⟩ := localizedBesselCommutator_family_l2_bound η₁ η' η₂ σ
    (fun j : Fin k => V j.succ) hη₁η' hη'η₂
  set K : ℝ := C8 * Cp + C8 * Cp * Real.sqrt (k : ℝ) + C8 * (C9 : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K ^ 2 + 3 * K, by positivity, fun i u => ?_⟩
  set φ := operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ) u
    with hφ
  set a := sobolevNorm σ (realMultiplierOperator η₂ (Hormander.C.diffusionOperator V cS u))
    with ha
  set b := sobolevNorm σ (realMultiplierOperator η₂ u) with hb
  set E := ∑ j : Fin k, sobolevNorm 0 (vectorFieldOperator (V j.succ) φ) ^ 2 with hE
  have ha0 : 0 ≤ a := sobolevNorm_nonneg _ _
  have hb0 : 0 ≤ b := sobolevNorm_nonneg _ _
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsum : ∑ j : Fin k, sobolevNorm 0 (vectorFieldOperator (V j.succ) φ) ≤
      Real.sqrt (k : ℝ) * Real.sqrt E :=
    sum_le_sqrt_card_mul_sqrt_sum_sq _ fun j => sobolevNorm_nonneg _ _
  have hφn : sobolevNorm 0 φ ≤ (C9 : ℝ) * b := h9 i u
  have hφ2 : sobolevNorm 0 φ ^ 2 ≤ ((C9 : ℝ) * b) ^ 2 :=
    pow_le_pow_left₀ (sobolevNorm_nonneg _ _) hφn 2
  have hpr := hp i u
  have hpr' : ‖hermitianPairing (Hormander.C.diffusionOperator V cS φ) φ‖ ≤
      Cp * (a * b + b * (Real.sqrt (k : ℝ) * Real.sqrt E) + b ^ 2) := by
    refine hpr.trans (mul_le_mul_of_nonneg_left ?_ hCp0)
    have := mul_le_mul_of_nonneg_left hsum hb0
    linarith
  have hEle : E ≤ C8 * (Cp * (a * b + b * (Real.sqrt (k : ℝ) * Real.sqrt E) + b ^ 2) +
      ((C9 : ℝ) * b) ^ 2) :=
    (h8 φ).trans (mul_le_mul_of_nonneg_left (add_le_add hpr' hφ2) hC80)
  have hsk : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
  have hsE : 0 ≤ Real.sqrt E := Real.sqrt_nonneg _
  have hEK : E ≤ K * (a * b + b * Real.sqrt E + b ^ 2) := by
    refine hEle.trans ?_
    have t1 : 0 ≤ a * b := mul_nonneg ha0 hb0
    have t2 : 0 ≤ b * Real.sqrt E := mul_nonneg hb0 hsE
    have t3 : 0 ≤ b ^ 2 := sq_nonneg b
    have p0 : 0 ≤ C8 * Cp := by positivity
    have p1 : 0 ≤ C8 * Cp * Real.sqrt (k : ℝ) := by positivity
    have p2 : 0 ≤ C8 * (C9 : ℝ) ^ 2 := by positivity
    have u1 : C8 * Cp * (a * b) ≤ K * (a * b) :=
      mul_le_mul_of_nonneg_right (by rw [hK]; linarith) t1
    have u2 : C8 * Cp * Real.sqrt (k : ℝ) * (b * Real.sqrt E) ≤ K * (b * Real.sqrt E) :=
      mul_le_mul_of_nonneg_right (by rw [hK]; linarith) t2
    have u3 : (C8 * Cp + C8 * (C9 : ℝ) ^ 2) * b ^ 2 ≤ K * b ^ 2 :=
      mul_le_mul_of_nonneg_right (by rw [hK]; linarith) t3
    nlinarith [u1, u2, u3]
  exact young_absorb_energy_bound hE0 ha0 hb0 hK0 hEK


/-- The diagonal sum bound, given the commutator energy bound as a
hypothesis. -/
theorem diagonal_commutator_sum_le_of_energy {N k : ℕ}
    (V : Fin (k + 1) → RealSchwartzVectorField N)
    (cS : SchwartzMap (Carrier N) ℝ) (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (σ : ℝ)
    (hE : ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin k) (u : TestFunction N),
      ∑ j : Fin k, sobolevNorm 0 (vectorFieldOperator (V j.succ)
          (operatorComm (vectorFieldOperator (V i.succ))
            (localizedBesselOperator η₁ η' σ) u)) ^ 2 ≤
        C * (sobolevNorm σ (realMultiplierOperator η₂ (Hormander.C.diffusionOperator V cS u)) ^ 2 +
          sobolevNorm σ (realMultiplierOperator η₂ u) ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : TestFunction N,
      ∑ i : Fin k, sobolevNorm 0 (vectorFieldOperator (V i.succ)
          (operatorComm (vectorFieldOperator (V i.succ))
            (localizedBesselOperator η₁ η' σ) u)) ≤
        C * (sobolevNorm σ (realMultiplierOperator η₂ (Hormander.C.diffusionOperator V cS u)) +
          sobolevNorm σ (realMultiplierOperator η₂ u)) := by
  obtain ⟨C10, hC100, h10⟩ := hE
  refine ⟨Real.sqrt (k : ℝ) * Real.sqrt ((k : ℝ) * C10), by positivity, fun u => ?_⟩
  set a := sobolevNorm σ (realMultiplierOperator η₂ (Hormander.C.diffusionOperator V cS u))
    with ha
  set b := sobolevNorm σ (realMultiplierOperator η₂ u) with hb
  have ha0 : 0 ≤ a := sobolevNorm_nonneg _ _
  have hb0 : 0 ≤ b := sobolevNorm_nonneg _ _
  set z : Fin k → Fin k → ℝ := fun i j => sobolevNorm 0 (vectorFieldOperator (V j.succ)
    (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ) u))
    with hz
  have hdiag := diagonal_sum_le_sqrt_card_mul_sqrt_full_energy z
    (fun i j => sobolevNorm_nonneg _ _)
  have hfull : ∑ i : Fin k, ∑ j : Fin k, (z i j) ^ 2 ≤ (k : ℝ) * C10 * (a + b) ^ 2 := by
    calc ∑ i : Fin k, ∑ j : Fin k, (z i j) ^ 2
        ≤ ∑ _i : Fin k, C10 * (a ^ 2 + b ^ 2) := Finset.sum_le_sum fun i _ => h10 i u
      _ = (k : ℝ) * C10 * (a ^ 2 + b ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ (k : ℝ) * C10 * (a + b) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_nonneg ha0 hb0]
  have hsqrt : Real.sqrt (∑ i : Fin k, ∑ j : Fin k, (z i j) ^ 2) ≤
      Real.sqrt ((k : ℝ) * C10) * (a + b) := by
    calc Real.sqrt (∑ i : Fin k, ∑ j : Fin k, (z i j) ^ 2)
        ≤ Real.sqrt ((k : ℝ) * C10 * (a + b) ^ 2) := Real.sqrt_le_sqrt hfull
      _ = Real.sqrt ((k : ℝ) * C10) * (a + b) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  calc ∑ i : Fin k, sobolevNorm 0 (vectorFieldOperator (V i.succ)
          (operatorComm (vectorFieldOperator (V i.succ))
            (localizedBesselOperator η₁ η' σ) u))
      = ∑ i : Fin k, z i i := rfl
    _ ≤ Real.sqrt (k : ℝ) * Real.sqrt (∑ i : Fin k, ∑ j : Fin k, (z i j) ^ 2) := hdiag
    _ ≤ Real.sqrt (k : ℝ) * (Real.sqrt ((k : ℝ) * C10) * (a + b)) :=
        mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
    _ = Real.sqrt (k : ℝ) * Real.sqrt ((k : ℝ) * C10) * (a + b) := by ring

/-- Each commutator `T_i u = [X_i, A] u` has full first-order energy
`∑_j ‖X_j T_i u‖₂²` bounded by the squared localized data norms. -/
theorem commutator_energy_le {N k : ℕ} (V : Fin (k + 1) → RealSchwartzVectorField N)
    (cS : SchwartzMap (Carrier N) ℝ) (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (σ : ℝ)
    (hη₁η' : cutoffPrecedes (η₁ : Carrier N → ℝ) (η' : Carrier N → ℝ))
    (hη'η₂ : cutoffPrecedes (η' : Carrier N → ℝ) (η₂ : Carrier N → ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin k) (u : TestFunction N),
      ∑ j : Fin k, sobolevNorm 0 (vectorFieldOperator (V j.succ)
          (operatorComm (vectorFieldOperator (V i.succ))
            (localizedBesselOperator η₁ η' σ) u)) ^ 2 ≤
        C * (sobolevNorm σ (realMultiplierOperator η₂ (Hormander.C.diffusionOperator V cS u)) ^ 2 +
          sobolevNorm σ (realMultiplierOperator η₂ u) ^ 2) :=
  commutator_energy_le_of_pairing V cS η₁ η' η₂ σ hη₁η' hη'η₂
    (energy_pairing_bound V cS η₁ η' η₂ σ hη₁η' hη'η₂)

/-- The diagonal first-order terms `∑_i ‖X_i T_i u‖₂` are controlled by
the localized data norms. -/
theorem diagonal_commutator_sum_le {N k : ℕ} (V : Fin (k + 1) → RealSchwartzVectorField N)
    (cS : SchwartzMap (Carrier N) ℝ) (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (σ : ℝ)
    (hη₁η' : cutoffPrecedes (η₁ : Carrier N → ℝ) (η' : Carrier N → ℝ))
    (hη'η₂ : cutoffPrecedes (η' : Carrier N → ℝ) (η₂ : Carrier N → ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : TestFunction N,
      ∑ i : Fin k, sobolevNorm 0 (vectorFieldOperator (V i.succ)
          (operatorComm (vectorFieldOperator (V i.succ))
            (localizedBesselOperator η₁ η' σ) u)) ≤
        C * (sobolevNorm σ (realMultiplierOperator η₂ (Hormander.C.diffusionOperator V cS u)) +
          sobolevNorm σ (realMultiplierOperator η₂ u)) :=
  diagonal_commutator_sum_le_of_energy V cS η₁ η' η₂ σ
    (commutator_energy_le V cS η₁ η' η₂ σ hη₁η' hη'η₂)

end Hormander.D

end

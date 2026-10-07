-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.D.LocalizedOrder
public import Hormander.D.CommExpansion
public import Hormander.C.Induction.L2
public import Hormander.C.Energy.Estimate

@[expose] public section

noncomputable section

namespace Hormander.D

open Hormander.B

/-- Expansion of `L (T u)` for `T = [X_i, A]`: it is `T (L u)` plus the
first-order terms `2 X_j [X_j, T] u`, the double commutators `[[X_j, T], X_j] u`, and the drift and
potential commutators `[X₀, T] u`, `[c, T] u`. -/
theorem diffusionOperator_comm_apply_decomp {N k : ℕ} (V : Fin (k + 1) → RealSchwartzVectorField N)
    (cS : SchwartzMap (Carrier N) ℝ) (A : Operator N) (i : Fin k) (u : TestFunction N) :
    Hormander.C.diffusionOperator V cS
        (operatorComm (vectorFieldOperator (V i.succ)) A u) =
      operatorComm (vectorFieldOperator (V i.succ)) A (Hormander.C.diffusionOperator V cS u) +
      ((∑ j : Fin k,
          (vectorFieldOperator (V j.succ) (operatorComm (vectorFieldOperator (V j.succ))
              (operatorComm (vectorFieldOperator (V i.succ)) A) u) +
            vectorFieldOperator (V j.succ) (operatorComm (vectorFieldOperator (V j.succ))
              (operatorComm (vectorFieldOperator (V i.succ)) A) u) +
          operatorComm (operatorComm (vectorFieldOperator (V j.succ))
              (operatorComm (vectorFieldOperator (V i.succ)) A)) (vectorFieldOperator (V j.succ)) u)) +
        operatorComm (vectorFieldOperator (V 0))
          (operatorComm (vectorFieldOperator (V i.succ)) A) u +
        operatorComm (realMultiplierOperator cS)
          (operatorComm (vectorFieldOperator (V i.succ)) A) u) := by
  have h := commutator_sum_squares_expansion (fun j : Fin k => vectorFieldOperator (V j.succ))
    (vectorFieldOperator (V 0)) (realMultiplierOperator cS)
    (operatorComm (vectorFieldOperator (V i.succ)) A)
  have h' : operatorComm (Hormander.C.diffusionOperator V cS)
      (operatorComm (vectorFieldOperator (V i.succ)) A) = _ := h
  have hu := LinearMap.congr_fun h' u
  have e : ∀ (P Q : Operator N) (w : TestFunction N),
      operatorComm P Q w = P (Q w) - Q (P w) := fun P Q w => rfl
  rw [e (Hormander.C.diffusionOperator V cS) _ u] at hu
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    two_smul] at hu
  rw [sub_eq_iff_eq_add'] at hu
  exact hu

/-- Pairing a vector-field image with a test function: after moving the
vector field across the Hermitian pairing, the pairing is bounded by the `L²` norm of the first
entry times the vector-field energy plus a zeroth-order term. -/
theorem vectorField_pairing_family_bound {N k : ℕ} (Y : Fin k → RealSchwartzVectorField N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin k) (w φ : TestFunction N),
      ‖hermitianPairing (vectorFieldOperator (Y j) w) φ‖ ≤
        sobolevNorm 0 w *
          (sobolevNorm 0 (vectorFieldOperator (Y j) φ) + C * sobolevNorm 0 φ) := by
  classical
  have hM : ∀ j, ∃ C : NNReal, ∀ φ : TestFunction N,
      sobolevNorm 0 (realMultiplierOperator (Hormander.C.negDiv (Y j)) φ) ≤
        (C : ℝ) * sobolevNorm 0 φ := by
    intro j
    obtain ⟨C, hC⟩ := (hasOrder_multiplierOperator_zero
      (complexifyRealSchwartz (Hormander.C.negDiv (Y j)))) 0
    exact ⟨C, fun φ => by simpa [realMultiplierOperator] using hC φ⟩
  choose Cj hCj using hM
  refine ⟨((Finset.univ.sup Cj : NNReal) : ℝ), NNReal.coe_nonneg _, fun j w φ => ?_⟩
  have hadj := Hormander.C.vectorField_hasHermitianAdjoint (Y j) w φ
  simp only [LinearMap.add_apply, LinearMap.neg_apply] at hadj
  rw [hadj]
  refine (Hormander.C.norm_H_le _ _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (sobolevNorm_nonneg _ _)
  have e : -(vectorFieldOperator (Y j)) φ +
      realMultiplierOperator (Hormander.C.negDiv (Y j)) φ =
      (-1 : ℂ) • vectorFieldOperator (Y j) φ +
        realMultiplierOperator (Hormander.C.negDiv (Y j)) φ := by
    simp
  rw [e]
  refine (sobolevNorm_add_le _ _ _).trans ?_
  rw [sobolevNorm_smul]
  have hCle : (Cj j : ℝ) ≤ ((Finset.univ.sup Cj : NNReal) : ℝ) := by
    exact_mod_cast Finset.le_sup (Finset.mem_univ j)
  have h1 := hCj j φ
  have h2 : (Cj j : ℝ) * sobolevNorm 0 φ ≤
      ((Finset.univ.sup Cj : NNReal) : ℝ) * sobolevNorm 0 φ :=
    mul_le_mul_of_nonneg_right hCle (sobolevNorm_nonneg _ _)
  simp only [norm_neg, norm_one, one_mul]
  linarith


/-- The energy pairing of `T_i u` with `L T_i u` is controlled by the localized
data norms and the vector-field energy of `T_i u`. -/
theorem energy_pairing_bound {N k : ℕ} (V : Fin (k + 1) → RealSchwartzVectorField N)
    (cS : SchwartzMap (Carrier N) ℝ) (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (σ : ℝ)
    (hη₁η' : cutoffPrecedes (η₁ : Carrier N → ℝ) (η' : Carrier N → ℝ))
    (hη'η₂ : cutoffPrecedes (η' : Carrier N → ℝ) (η₂ : Carrier N → ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin k) (u : TestFunction N),
      ‖hermitianPairing (Hormander.C.diffusionOperator V cS
          (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ) u))
        (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ) u)‖ ≤
      C * (sobolevNorm σ (realMultiplierOperator η₂ (Hormander.C.diffusionOperator V cS u)) *
            sobolevNorm σ (realMultiplierOperator η₂ u) +
          sobolevNorm σ (realMultiplierOperator η₂ u) *
            ∑ j : Fin k, sobolevNorm 0 (vectorFieldOperator (V j.succ)
              (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ) u)) +
          sobolevNorm σ (realMultiplierOperator η₂ u) ^ 2) := by
  classical
  obtain ⟨⟨CT, hCT⟩, ⟨CU, hCU⟩, ⟨CW, hCW⟩, ⟨CD, hCD⟩, ⟨CC, hCC⟩⟩ :=
    localizedBesselEnergyComm_l2_bounds η₁ η' η₂ σ (fun j : Fin k => V j.succ) (V 0) cS
      hη₁η' hη'η₂
  obtain ⟨CM, hCM0, hCM⟩ := vectorField_pairing_family_bound (fun j : Fin k => V j.succ)
  have hT0 : 0 ≤ (CT : ℝ) := CT.2
  have hU0 : 0 ≤ (CU : ℝ) := CU.2
  have hW0 : 0 ≤ (CW : ℝ) := CW.2
  have hD0 : 0 ≤ (CD : ℝ) := CD.2
  have hC0 : 0 ≤ (CC : ℝ) := CC.2
  set p₁ : ℝ := (CT : ℝ) * CT with hp₁
  set p₂ : ℝ := 2 * CU with hp₂
  set p₃ : ℝ := (k : ℝ) * (2 * CU * CM * CT + CW * CT) + CD * CT + CC * CT with hp₃
  have hp₁0 : 0 ≤ p₁ := by positivity
  have hp₂0 : 0 ≤ p₂ := by positivity
  have hp₃0 : 0 ≤ p₃ := by positivity
  refine ⟨p₁ + p₂ + p₃, by positivity, fun i u => ?_⟩
  rw [diffusionOperator_comm_apply_decomp V cS (localizedBesselOperator η₁ η' σ) i u]
  set A₀ := sobolevNorm σ (realMultiplierOperator η₂ (Hormander.C.diffusionOperator V cS u))
    with hA₀def
  set B := sobolevNorm σ (realMultiplierOperator η₂ u) with hBdef
  set φ := operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ) u
    with hφdef
  have hA₀ : 0 ≤ A₀ := sobolevNorm_nonneg _ _
  have hB : 0 ≤ B := sobolevNorm_nonneg _ _
  have hφ : sobolevNorm 0 φ ≤ CT * B := hCT i u
  have hφ0 : 0 ≤ sobolevNorm 0 φ := sobolevNorm_nonneg _ _
  set x : Fin k → ℝ := fun j => sobolevNorm 0 (vectorFieldOperator (V j.succ) φ) with hxdef
  have hx0 : ∀ j, 0 ≤ x j := fun j => sobolevNorm_nonneg _ _
  simp only [Hormander.C.H_add_left, Hormander.C.H_sum_left]
  -- the transported term `T_i (L u)`
  have bTl : ‖hermitianPairing (operatorComm (vectorFieldOperator (V i.succ))
      (localizedBesselOperator η₁ η' σ) (Hormander.C.diffusionOperator V cS u)) φ‖ ≤
      p₁ * (A₀ * B) := by
    refine (Hormander.C.norm_H_le _ _).trans ?_
    have h1 : sobolevNorm 0 (operatorComm (vectorFieldOperator (V i.succ))
        (localizedBesselOperator η₁ η' σ) (Hormander.C.diffusionOperator V cS u)) ≤
        CT * A₀ := hCT i _
    calc _ ≤ ((CT : ℝ) * A₀) * (CT * B) :=
          mul_le_mul h1 hφ hφ0 (mul_nonneg hT0 hA₀)
      _ = p₁ * (A₀ * B) := by rw [hp₁]; ring
  -- the first-order terms
  have bX : ∀ j : Fin k, ‖hermitianPairing (vectorFieldOperator (V j.succ)
      (operatorComm (vectorFieldOperator (V j.succ))
        (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ)) u))
      φ‖ ≤ (CU * B) * (x j + CM * (CT * B)) := by
    intro j
    refine (hCM j _ φ).trans ?_
    have h1 : sobolevNorm 0 (operatorComm (vectorFieldOperator (V j.succ))
        (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ)) u) ≤
        CU * B := hCU i j u
    have h2 : x j + CM * sobolevNorm 0 φ ≤ x j + CM * (CT * B) := by
      have := mul_le_mul_of_nonneg_left hφ hCM0
      linarith
    exact mul_le_mul h1 h2 (add_nonneg (hx0 j) (mul_nonneg hCM0 hφ0)) (by positivity)
  have bW : ∀ j : Fin k, ‖hermitianPairing (operatorComm
      (operatorComm (vectorFieldOperator (V j.succ))
        (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ)))
      (vectorFieldOperator (V j.succ)) u) φ‖ ≤ (CW * B) * (CT * B) := by
    intro j
    refine (Hormander.C.norm_H_le _ _).trans ?_
    have h1 : sobolevNorm 0 (operatorComm
        (operatorComm (vectorFieldOperator (V j.succ))
          (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ)))
        (vectorFieldOperator (V j.succ)) u) ≤ CW * B := hCW i j u
    exact mul_le_mul h1 hφ hφ0 (by positivity)
  have bD : ‖hermitianPairing (operatorComm (vectorFieldOperator (V 0))
      (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ)) u)
      φ‖ ≤ (CD * B) * (CT * B) := by
    refine (Hormander.C.norm_H_le _ _).trans ?_
    have h1 : sobolevNorm 0 (operatorComm (vectorFieldOperator (V 0))
        (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ)) u) ≤
        CD * B := hCD i u
    exact mul_le_mul h1 hφ hφ0 (by positivity)
  have bC : ‖hermitianPairing (operatorComm (realMultiplierOperator cS)
      (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ)) u)
      φ‖ ≤ (CC * B) * (CT * B) := by
    refine (Hormander.C.norm_H_le _ _).trans ?_
    have h1 : sobolevNorm 0 (operatorComm (realMultiplierOperator cS)
        (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ)) u) ≤
        CC * B := hCC i u
    exact mul_le_mul h1 hφ hφ0 (by positivity)
  have bS : ‖∑ j : Fin k,
      (hermitianPairing (vectorFieldOperator (V j.succ)
        (operatorComm (vectorFieldOperator (V j.succ))
          (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ)) u)) φ +
      hermitianPairing (vectorFieldOperator (V j.succ)
        (operatorComm (vectorFieldOperator (V j.succ))
          (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ)) u)) φ +
      hermitianPairing (operatorComm
        (operatorComm (vectorFieldOperator (V j.succ))
          (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ)))
        (vectorFieldOperator (V j.succ)) u) φ)‖ ≤
      p₂ * (B * ∑ j, x j) + ((k : ℝ) * (2 * CU * CM * CT + CW * CT)) * B ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    have hj : ∀ j ∈ (Finset.univ : Finset (Fin k)),
        ‖hermitianPairing (vectorFieldOperator (V j.succ)
          (operatorComm (vectorFieldOperator (V j.succ))
            (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ))
              u)) φ +
        hermitianPairing (vectorFieldOperator (V j.succ)
          (operatorComm (vectorFieldOperator (V j.succ))
            (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ))
              u)) φ +
        hermitianPairing (operatorComm
          (operatorComm (vectorFieldOperator (V j.succ))
            (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ)))
          (vectorFieldOperator (V j.succ)) u) φ‖ ≤
        (2 * CU * B) * x j + (2 * CU * CM * CT + CW * CT) * B ^ 2 := by
      intro j _
      refine (norm_add₃_le).trans ?_
      have h1 := bX j
      have h2 := bW j
      nlinarith [h1, h2]
    refine (Finset.sum_le_sum hj).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hp₂]
    apply le_of_eq
    ring
  have ha : 0 ≤ A₀ * B := mul_nonneg hA₀ hB
  have hb : 0 ≤ B * ∑ j, x j := mul_nonneg hB (Finset.sum_nonneg fun j _ => hx0 j)
  have hc : 0 ≤ B ^ 2 := sq_nonneg B
  calc _ ≤ ‖hermitianPairing (operatorComm (vectorFieldOperator (V i.succ))
        (localizedBesselOperator η₁ η' σ) (Hormander.C.diffusionOperator V cS u)) φ‖ +
        (‖∑ j : Fin k,
      (hermitianPairing (vectorFieldOperator (V j.succ)
        (operatorComm (vectorFieldOperator (V j.succ))
          (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ)) u)) φ +
      hermitianPairing (vectorFieldOperator (V j.succ)
        (operatorComm (vectorFieldOperator (V j.succ))
          (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ)) u)) φ +
      hermitianPairing (operatorComm
        (operatorComm (vectorFieldOperator (V j.succ))
          (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ)))
        (vectorFieldOperator (V j.succ)) u) φ)‖ +
        ‖hermitianPairing (operatorComm (vectorFieldOperator (V 0))
      (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ)) u)
      φ‖ +
        ‖hermitianPairing (operatorComm (realMultiplierOperator cS)
      (operatorComm (vectorFieldOperator (V i.succ)) (localizedBesselOperator η₁ η' σ)) u)
      φ‖) := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add₃_le
    _ ≤ p₁ * (A₀ * B) + ((p₂ * (B * ∑ j, x j) + ((k : ℝ) * (2 * CU * CM * CT + CW * CT)) * B ^ 2) +
        (CD * B) * (CT * B) + (CC * B) * (CT * B)) := by
        gcongr
    _ = p₁ * (A₀ * B) + p₂ * (B * ∑ j, x j) + p₃ * B ^ 2 := by rw [hp₃]; ring
    _ ≤ (p₁ + p₂ + p₃) * (A₀ * B + B * ∑ j, x j + B ^ 2) := by
        nlinarith [mul_nonneg (add_nonneg hp₂0 hp₃0) ha, mul_nonneg (add_nonneg hp₁0 hp₃0) hb,
          mul_nonneg (add_nonneg hp₁0 hp₂0) hc]

end Hormander.D

end

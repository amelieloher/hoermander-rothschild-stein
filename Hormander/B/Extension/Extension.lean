-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Extension.Conjugation
public import Hormander.A.Scale.Riesz

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped ComplexConjugate FourierTransform

namespace Hormander.B

/-- Duality bound with the dual index named separately (`τ = -σ`). -/
theorem abs_pairing_le_dual {N : ℕ} {σ τ : ℝ} (hτ : τ = -σ) (u : BesselPotentialSpace (Carrier N) ℂ σ 2)
    (ψ : TestFunction N) :
    ‖u.toDistr ψ‖ ≤ ‖u‖ * ‖Hormander.A.schwartzToSobolev τ ψ‖ := by
  have : σ = -τ := by linarith
  subst this
  exact Hormander.A.abs_pairing_le τ u ψ

/-- Converse duality with the dual index named separately (`τ = -r`). -/
theorem riesz_converse_dual {N : ℕ} {r τ : ℝ} (hτ : τ = -r) (u : Tempered N) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ φ : TestFunction N, ‖u φ‖ ≤ C * ‖Hormander.A.schwartzToSobolev τ φ‖) :
    ∃ v : BesselPotentialSpace (Carrier N) ℂ r 2, v.toDistr = u ∧ ‖v‖ ≤ C := by
  have : r = -τ := by linarith
  subst this
  exact Hormander.A.riesz_converse τ u hC h

/-- A Schwartz function, viewed as a tempered distribution, acts by the bilinear pairing. -/
theorem testToTempered_apply {N : ℕ} (u φ : TestFunction N) :
    (u : Tempered N) φ = bilinearPairing φ u := by
  rw [SchwartzMap.coe_apply]
  simp [bilinearPairing, smul_eq_mul]


/-- Duality: an order estimate for `T` at index `r` gives the dual estimate for the transpose,
`‖T^t φ‖_{H^{-(r+m)}} ≤ C ‖φ‖_{H^{-r}}`, with the same constant. -/
theorem transpose_bound_of_bound {N : ℕ} {T Tt : Operator N} (hT : HasBilinearTranspose T Tt)
    {m r : ℝ} {C : NNReal}
    (hC : ∀ φ : TestFunction N, sobolevNorm r (T φ) ≤ (C : ℝ) * sobolevNorm (r + m) φ)
    (φ : TestFunction N) :
    sobolevNorm (-(r + m)) (Tt φ) ≤ (C : ℝ) * sobolevNorm (-r) φ := by
  have hB : 0 ≤ (C : ℝ) * sobolevNorm (-r) φ := mul_nonneg C.2 (sobolevNorm_nonneg _ _)
  have hbound : ∀ ψ : TestFunction N, ‖((Tt φ : TestFunction N) : Tempered N) ψ‖ ≤
      ((C : ℝ) * sobolevNorm (-r) φ) * ‖Hormander.A.schwartzToSobolev (r + m) ψ‖ := by
    intro ψ
    rw [testToTempered_apply]
    have h1 : bilinearPairing ψ (Tt φ) = ((Hormander.A.schwartzToSobolev (-r) φ).toDistr) (T ψ) := by
      have : (Hormander.A.schwartzToSobolev (-r) φ).toDistr = (φ : Tempered N) :=
        TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr _
      rw [this, testToTempered_apply, bilinearPairing_comm, hT]
      exact bilinearPairing_comm _ _
    rw [h1]
    refine (Hormander.A.abs_pairing_le r (Hormander.A.schwartzToSobolev (-r) φ) (T ψ)).trans ?_
    have h2 := hC ψ
    calc ‖Hormander.A.schwartzToSobolev (-r) φ‖ * ‖Hormander.A.schwartzToSobolev r (T ψ)‖
        ≤ ‖Hormander.A.schwartzToSobolev (-r) φ‖ * ((C : ℝ) * ‖Hormander.A.schwartzToSobolev (r + m) ψ‖) := by
          apply mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ((C : ℝ) * sobolevNorm (-r) φ) * ‖Hormander.A.schwartzToSobolev (r + m) ψ‖ := by
          rw [sobolevNorm_eq_schwartzToSobolev_norm]; ring
  obtain ⟨v, hv1, hv2⟩ := Hormander.A.riesz_converse (r + m) _ hB hbound
  have : v = Hormander.A.schwartzToSobolev (-(r + m)) (Tt φ) := by
    apply BesselPotentialSpace.ext
    rw [hv1]
    exact (TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr _).symm
  rw [sobolevNorm_eq_schwartzToSobolev_norm, ← this]
  exact hv2


/-- The transposed operator as a continuous linear map on `𝓢`, given its continuity. -/
def continuousTranspose {N : ℕ} (Tt : Operator N) (hc : Continuous Tt) :
    TestFunction N →L[ℂ] TestFunction N :=
  { Tt with cont := hc }

/-- The transposition extension `T'` to tempered distributions, `⟨T'u, φ⟩ = ⟨u, T^t φ⟩`. -/
def tempExtension {N : ℕ} (Tt : Operator N) (hc : Continuous Tt) : Tempered N →L[ℂ] Tempered N :=
  transposeExtension (continuousTranspose Tt hc)

/-- Defining identity of the extension. -/
theorem tempExtension_apply_apply {N : ℕ} (Tt : Operator N) (hc : Continuous Tt)
    (u : Tempered N) (φ : TestFunction N) : tempExtension Tt hc u φ = u (Tt φ) := rfl

/-- The extension `T'` agrees with `T` on `𝓢`. -/
theorem tempExtension_test {N : ℕ} {T Tt : Operator N} (hT : HasBilinearTranspose T Tt)
    (hc : Continuous Tt) (u : TestFunction N) :
    tempExtension Tt hc (u : Tempered N) = ((T u : TestFunction N) : Tempered N) := by
  ext φ
  rw [tempExtension_apply_apply, testToTempered_apply, testToTempered_apply, bilinearPairing_comm,
    ← hT, bilinearPairing_comm]

/-- Sobolev extension: if `‖T φ‖_{H^r} ≤ C ‖φ‖_{H^{r+m}}` on `𝓢` (the order constant
`C_r(T)`), then `T'` maps `H^{r+m}` into `H^r` with `‖T'u‖_{H^r} ≤ C ‖u‖_{H^{r+m}}`. -/
theorem tempExtension_sobolev {N : ℕ} {T Tt : Operator N} (hT : HasBilinearTranspose T Tt)
    (hc : Continuous Tt) {m r : ℝ} {C : NNReal}
    (hC : ∀ φ : TestFunction N, sobolevNorm r (T φ) ≤ (C : ℝ) * sobolevNorm (r + m) φ)
    (u : BesselPotentialSpace (Carrier N) ℂ (r + m) 2) :
    ∃ v : BesselPotentialSpace (Carrier N) ℂ r 2,
      v.toDistr = tempExtension Tt hc u.toDistr ∧ ‖v‖ ≤ (C : ℝ) * ‖u‖ := by
  refine riesz_converse_dual (r := r) (τ := -r) rfl _ (mul_nonneg C.2 (norm_nonneg _)) ?_
  intro φ
  rw [tempExtension_apply_apply]
  refine (abs_pairing_le_dual (σ := r + m) (τ := -(r + m)) rfl u (Tt φ)).trans ?_
  have := transpose_bound_of_bound hT hC φ
  rw [sobolevNorm_eq_schwartzToSobolev_norm, sobolevNorm_eq_schwartzToSobolev_norm] at this
  calc ‖u‖ * ‖Hormander.A.schwartzToSobolev (-(r + m)) (Tt φ)‖
      ≤ ‖u‖ * ((C : ℝ) * ‖Hormander.A.schwartzToSobolev (-r) φ‖) :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = ((C : ℝ) * ‖u‖) * ‖Hormander.A.schwartzToSobolev (-r) φ‖ := by ring


/-- Global extension to tempered distributions and Sobolev spaces. For `T` with a
continuous bilinear transpose `T^t` and order `m`, transposition defines a continuous
`T': 𝓢' → 𝓢'` with `⟨T'u, φ⟩ = ⟨u, T^t φ⟩`, agreeing with `T` on `𝓢`, and for every
`r` there is a constant `C` (the Schwartz order constant of `T` at index `r`) with
`T': H^{r+m} → H^r`, `‖T'u‖_{H^r} ≤ C ‖u‖_{H^{r+m}}`. -/
theorem global_extension {N : ℕ} {T Tt : Operator N} (hT : HasBilinearTranspose T Tt)
    (hc : Continuous Tt) {m : ℝ} (hord : HasOrder m T) :
    (∀ (u : Tempered N) (φ : TestFunction N), tempExtension Tt hc u φ = u (Tt φ)) ∧
      (∀ u : TestFunction N, tempExtension Tt hc (u : Tempered N) = ((T u : TestFunction N) : Tempered N)) ∧
      ∀ r : ℝ, ∃ C : NNReal,
        (∀ φ : TestFunction N, sobolevNorm r (T φ) ≤ (C : ℝ) * sobolevNorm (r + m) φ) ∧
        ∀ u : BesselPotentialSpace (Carrier N) ℂ (r + m) 2,
          ∃ v : BesselPotentialSpace (Carrier N) ℂ r 2,
            v.toDistr = tempExtension Tt hc u.toDistr ∧ ‖v‖ ≤ (C : ℝ) * ‖u‖ := by
  refine ⟨fun u φ => tempExtension_apply_apply Tt hc u φ,
    fun u => tempExtension_test hT hc u, fun r => ?_⟩
  obtain ⟨C, hC⟩ := hord r
  exact ⟨C, hC, fun u => tempExtension_sobolev hT hc hC u⟩

end Hormander.B

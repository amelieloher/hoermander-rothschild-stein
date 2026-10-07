-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.D.Assembly.C9Step
public import Hormander.D.Assembly.CommutatorStep
public import Hormander.D.Assembly.EnergyAbsorption
public import Hormander.D.OffDiagonalLocalization
public import Hormander.D.Cutoffs
public import Hormander.B.Mollifier.EFacing

/-!
# Localized gain from the energy and commutator estimates

For complex Schwartz `u`, the localized gain
`‖η₁ u‖_{H^{σ+ε}} ≤ C (‖η₂ L̃ u‖_{H^σ} + ‖η₂ u‖_{H^σ})`
follows from the subelliptic estimate, the commutator bound, energy absorption, and an
off-diagonal smoothing hypothesis. The energy estimate and subelliptic estimate apply directly
to complex `u`.
-/

@[expose] public section

noncomputable section

open SchwartzMap
open Hormander.B

namespace Hormander.D

/-- For nested
cutoffs `ψ ≺ φ`, the separated Bessel tail `(1 - φ) Λ^σ ψ` maps `H^{r - τ}` to `H^r` for every
`r` and `τ`. It is the hypothesis of `localizedSobolev_offDiagonal_bound_of_B8`. -/
def OffDiagonalSmoothing (N : ℕ) : Prop :=
  ∀ (φ ψ : SchwartzMap (Carrier N) ℝ) (σ τ r : ℝ),
    cutoffPrecedes (ψ : Carrier N → ℝ) (φ : Carrier N → ℝ) →
    ∃ C : NNReal, ∀ v : TestFunction N,
      sobolevNorm r (offDiagonalTailOperator φ ψ σ v) ≤ (C : ℝ) * sobolevNorm (r - τ) v

/-- The localized gain for complex Schwartz inputs, assuming the off-diagonal smoothing bound. -/
theorem localized_gain_of_offDiagonal {k N : ℕ}
    (X : Fin (k + 1) → Hormander.B.Carrier N → Hormander.B.Carrier N)
    (c : Hormander.B.Carrier N → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hcc : HasCompactSupport c)
    {K U : Set (Hormander.B.Carrier N)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (s : ℕ) (hs : 1 ≤ s)
    (w : Fin N → Hormander.Interface.LieWord k)
    (hws : ∀ a, Hormander.lieWordLength (w a) ≤ s)
    (hw : ∀ x ∈ U,
      LinearIndependent ℝ (fun a => Hormander.lieWordEval X (w a) x))
    (η₁ η₂ : SchwartzMap (Hormander.B.Carrier N) ℝ)
    (hη : cutoffPrecedes (η₁ : Hormander.B.Carrier N → ℝ)
      (η₂ : Hormander.B.Carrier N → ℝ))
    (hη₂K : tsupport (η₂ : Hormander.B.Carrier N → ℝ) ⊆ K)
    (σ : ℝ) (hB8 : OffDiagonalSmoothing N) :
    ∃ C : ℝ, ∀ u : Hormander.B.TestFunction N,
      Hormander.B.sobolevNorm (σ + (2 : ℝ) / 4 ^ s)
        (Hormander.B.realMultiplierOperator η₁ u) ≤
        C * (Hormander.B.sobolevNorm σ
          (Hormander.B.realMultiplierOperator η₂
            (Hormander.C.diffusionOperator
              (Hormander.C.c9SchwartzVectorField X hX hXc)
              (Hormander.C.c9SchwartzMultiplier c hc hcc) u)) +
          Hormander.B.sobolevNorm σ
            (Hormander.B.realMultiplierOperator η₂ u)) := by
  -- a Schwartz cutoff strictly between `η₁` and `η₂`
  obtain ⟨ηf, h₁f, hf₂, -⟩ := exists_intermediate_cutoff hη
  let η' : SchwartzMap (Carrier N) ℝ := Hormander.B.cutoffSchwartzOuter h₁f
  have hη'coe : (η' : Carrier N → ℝ) = ηf := rfl
  have hη₁η' : cutoffPrecedes (η₁ : Carrier N → ℝ) (η' : Carrier N → ℝ) := by
    rw [hη'coe]; exact h₁f
  have hη'η₂ : cutoffPrecedes (η' : Carrier N → ℝ) (η₂ : Carrier N → ℝ) := by
    rw [hη'coe]; exact hf₂
  set V := Hormander.C.c9SchwartzVectorField X hX hXc
  set cS := Hormander.C.c9SchwartzMultiplier c hc hcc
  obtain ⟨C₅, hC₅⟩ := localizedSobolev_offDiagonal_bound_of_B8 hB8 η₁ η' η₂ σ
    ((2 : ℝ) / 4 ^ s) hη₁η' hη'η₂
  obtain ⟨C₄, hC₄0, hC₄⟩ := localized_bessel_gain_bound X c hX hXc hc hcc hK hU hKU s hs w hws
    hw η₁ η' η₂ σ hη₁η' hη'η₂ hη₂K
  obtain ⟨C₇, hC₇0, hC₇⟩ := commutator_l2_bound V cS η₁ η' η₂ σ hη₁η' hη'η₂
  obtain ⟨Cf, hCf0, hCf⟩ := diagonal_commutator_sum_le V cS η₁ η' η₂ σ hη₁η' hη'η₂
  refine ⟨C₄ * (2 + 2 * Cf + C₇) + (C₅ : ℝ), fun u => ?_⟩
  set A₀ := sobolevNorm σ (realMultiplierOperator η₂ (Hormander.C.diffusionOperator V cS u))
  set B₀ := sobolevNorm σ (realMultiplierOperator η₂ u)
  set Q := sobolevNorm 0 (operatorComm (Hormander.C.diffusionOperator V cS)
    (localizedBesselOperator η₁ η' σ) u)
  set D := ∑ j : Fin k, sobolevNorm 0 (vectorFieldOperator (V j.succ)
    (operatorComm (vectorFieldOperator (V j.succ)) (localizedBesselOperator η₁ η' σ) u))
  have hA₀ : 0 ≤ A₀ := sobolevNorm_nonneg _ _
  have hB₀ : 0 ≤ B₀ := sobolevNorm_nonneg _ _
  have h5 := hC₅ u
  have h4 : sobolevNorm ((2 : ℝ) / 4 ^ s) (localizedBesselOperator η₁ η' σ u) ≤
      C₄ * (A₀ + Q + B₀) := hC₄ u
  have h7 : Q ≤ 2 * D + C₇ * B₀ := hC₇ u
  have hf : D ≤ Cf * (A₀ + B₀) := hCf u
  have hQ : Q ≤ 2 * Cf * (A₀ + B₀) + C₇ * B₀ := by nlinarith
  have hinner : A₀ + Q + B₀ ≤ (2 + 2 * Cf + C₇) * (A₀ + B₀) := by nlinarith
  calc sobolevNorm (σ + (2 : ℝ) / 4 ^ s) (realMultiplierOperator η₁ u)
      ≤ sobolevNorm ((2 : ℝ) / 4 ^ s) (localizedBesselOperator η₁ η' σ u) + (C₅ : ℝ) * B₀ := h5
    _ ≤ C₄ * ((2 + 2 * Cf + C₇) * (A₀ + B₀)) + (C₅ : ℝ) * (A₀ + B₀) := by
        gcongr
        · exact h4.trans (mul_le_mul_of_nonneg_left hinner hC₄0)
        · linarith
    _ = (C₄ * (2 + 2 * Cf + C₇) + (C₅ : ℝ)) * (A₀ + B₀) := by ring

end Hormander.D

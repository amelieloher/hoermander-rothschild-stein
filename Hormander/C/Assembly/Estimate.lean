-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Assembly.FrameBound

@[expose] public section

noncomputable section
open MeasureTheory SchwartzMap FourierTransform
namespace Hormander.C
open Hormander.B
variable {N k : ℕ}

/-- The frame coordinate inequality (statement of `coordinate_sobolev_inequality_of_frame`). -/
def CoordinateInequality (N : ℕ) : Prop :=
  ∀ {K U : Set (Hormander.A.Carrier N)}, IsCompact K → IsOpen U → K ⊆ U →
    ∀ (V : Fin N → RealSchwartzVectorField N),
      (∀ x ∈ U, LinearIndependent ℝ (fun a : Fin N => fieldVec (V a) x)) →
      ∀ {δ : ℝ}, 0 < δ → δ < 1 →
        ∃ C : ℝ, 0 < C ∧ ∀ (u : SchwartzMap (Hormander.A.Carrier N) ℂ),
          tsupport (u : Hormander.A.Carrier N → ℂ) ⊆ K →
            Hormander.A.schwartzSobolevNorm δ u ^ 2 ≤
              C * (‖u.toLp 2‖ ^ 2 + ∑ a : Fin N, Hormander.A.schwartzSobolevNorm (δ - 1)
                (vectorFieldOperator (V a) u) ^ 2)

/-- The local basic subelliptic estimate follows from the closure facts, horizontal recurrence,
and frame coordinate inequality. -/
theorem subelliptic_estimate_of_inputs {k N : ℕ}
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (Xs : Fin (k + 1) → RealSchwartzVectorField N) (hXs : ∀ i x j, Xs i j x = X i x j)
    (cs : SchwartzMap (Carrier N) ℝ) (hcs : ∀ x, cs x = c x)
    (F : B10Facts N) (hH : HorizontalRecurrence Xs) (hCoord : CoordinateInequality N)
    {K U : Set (EuclideanSpace ℝ (Fin N))} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (s : ℕ) (hs : 1 ≤ s) (w : Fin N → Hormander.Interface.LieWord k)
    (hws : ∀ a, Hormander.lieWordLength (w a) ≤ s)
    (hw : ∀ x ∈ U, LinearIndependent ℝ (fun a => Hormander.lieWordEval X (w a) x)) :
    ∃ C : ℝ, ∀ u : 𝓢(EuclideanSpace ℝ (Fin N), ℂ), tsupport u ⊆ K →
      (∫ ξ, (1 + ‖ξ‖ ^ 2) ^ ((2 : ℝ) / 4 ^ s) * ‖𝓕 (⇑u) ξ‖ ^ 2) ≤
        C * ((∫ x, ‖(∑ i : Fin k,
                fderiv ℝ (fun y => fderiv ℝ u y (X i.succ y)) x (X i.succ x)) +
              fderiv ℝ u x (X 0 x) + (c x : ℂ) * u x‖ ^ 2) +
            ∫ x, ‖u x‖ ^ 2) := by
  set ε : ℝ := (2 : ℝ) / 4 ^ s with hε
  have hpow : (4 : ℝ) ≤ 4 ^ s := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ s := pow_le_pow_right₀ (by norm_num) hs
  have hε0 : 0 < ε := by positivity
  have hε1 : ε < 1 := by
    rw [hε, div_lt_one (by positivity)]; linarith
  -- the Schwartz frame
  set Vw : Fin N → RealSchwartzVectorField N := fun a => combField Xs (binaryExpansion (w a)) with hVw
  have hfv : ∀ a, fieldVec (Vw a) = Hormander.lieWordEval X (w a) := fun a => by
    rw [hVw]; dsimp only
    rw [combField_fieldVec Xs X hXs, binaryExpansion_eval X hX]
  have hframe : ∀ x ∈ U, LinearIndependent ℝ (fun a : Fin N => fieldVec (Vw a) x) := by
    intro x hx
    have := hw x hx
    simpa [hfv] using this
  obtain ⟨C4, hC40, hC4⟩ := hCoord hK hU hKU Vw hframe hε0 hε1
  obtain ⟨C8, hC80, hgain⟩ := drift_word_estimate_gain_of_B10 F Xs cs hH s
  have hM : ∀ a, ∃ M : ℝ, 0 ≤ M ∧ ∀ u : TestFunction N,
      sobolevNorm (ε - 1) (vectorFieldOperator (Vw a) u) ^ 2 ≤
        M * (normSq (diffusionOperator Xs cs u) + normSq u) := fun a =>
    frame_word_bound Xs cs hC80.le (fun ℓ h1 h2 => hgain ℓ h1 h2) (w a) (hws a)
  choose M hM0 hMb using hM
  have hMs : 0 ≤ ∑ a, M a := Finset.sum_nonneg fun a _ => hM0 a
  refine ⟨C4 * (1 + ∑ a, M a), fun u hu => ?_⟩
  have h1 := hC4 u hu
  have hL2 : ‖u.toLp 2‖ ^ 2 = normSq u := by
    rw [← sobolevNorm_zero_sq, sobolevNorm_zero_order]
  have hsum : ∑ a : Fin N, Hormander.A.schwartzSobolevNorm (ε - 1) (vectorFieldOperator (Vw a) u) ^ 2 ≤
      (∑ a, M a) * (normSq (diffusionOperator Xs cs u) + normSq u) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← sobolevNorm_eq_schwartzSobolevNorm]
    exact hMb a u
  have hQ0 : 0 ≤ normSq (diffusionOperator Xs cs u) + normSq u :=
    add_nonneg (normSq_nonneg _) (normSq_nonneg _)
  have hlhs : (∫ ξ, (1 + ‖ξ‖ ^ 2) ^ ε * ‖𝓕 (⇑u) ξ‖ ^ 2) =
      Hormander.A.schwartzSobolevNorm ε u ^ 2 := by
    rw [← weightedFourierSq_eq_schwartzSobolevNorm_sq]; rfl
  have hrhs : (∫ x, ‖(∑ i : Fin k,
                fderiv ℝ (fun y => fderiv ℝ u y (X i.succ y)) x (X i.succ x)) +
              fderiv ℝ u x (X 0 x) + (c x : ℂ) * u x‖ ^ 2) = normSq (diffusionOperator Xs cs u) := by
    unfold normSq
    congr 1; funext x
    rw [diffusionOperator_apply_pointwise Xs X hXs cs c hcs u x]
  have hnorm : (∫ x, ‖u x‖ ^ 2) = normSq u := rfl
  rw [hlhs, hrhs, hnorm]
  refine h1.trans ?_
  rw [hL2]
  calc C4 * (normSq u + ∑ a : Fin N, Hormander.A.schwartzSobolevNorm (ε - 1) (vectorFieldOperator (Vw a) u) ^ 2)
      ≤ C4 * (normSq u + (∑ a, M a) * (normSq (diffusionOperator Xs cs u) + normSq u)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) hC40.le
    _ ≤ C4 * (1 + ∑ a, M a) * (normSq (diffusionOperator Xs cs u) + normSq u) := by
        have h2 : normSq u ≤ normSq (diffusionOperator Xs cs u) + normSq u := by
          linarith [normSq_nonneg (diffusionOperator Xs cs u)]
        have h3 := mul_le_mul_of_nonneg_left h2 hC40.le
        nlinarith [mul_nonneg hC40.le (mul_nonneg hMs hQ0)]

end Hormander.C

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.D.ConditionalGain
public import Hormander.D.C9NormBridge
public import Hormander.C.Assembly.Final
public import Hormander.C.Assembly.Bridge
public import Hormander.C.C9Bridges
public import Hormander.C.Induction.L2

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap FourierTransform
open Hormander.Interface
open Hormander.B

namespace Hormander.D

/-- The Schwartz realization of the subelliptic operator, built from the Schwartz representatives
of the compactly supported smooth coefficients, has the displayed pointwise integrand. -/
theorem c9_diffusionOperator_apply {k N : ℕ}
    (X : Fin (k + 1) → Hormander.B.Carrier N → Hormander.B.Carrier N)
    (c : Hormander.B.Carrier N → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    (u : Hormander.B.TestFunction N) (x : Hormander.B.Carrier N) :
    Hormander.C.diffusionOperator (Hormander.C.c9SchwartzVectorField X hX hXc)
        (Hormander.C.c9SchwartzMultiplier c hc hcc) u x =
      (∑ i : Fin k, fderiv ℝ (fun y => fderiv ℝ (u : Hormander.B.Carrier N → ℂ) y
          (X i.succ y)) x (X i.succ x)) +
        fderiv ℝ (u : Hormander.B.Carrier N → ℂ) x (X 0 x) + (c x : ℂ) * u x :=
  Hormander.C.diffusionOperator_apply_pointwise
    (Hormander.C.c9SchwartzVectorField X hX hXc) X
    (fun _ _ _ => rfl) (Hormander.C.c9SchwartzMultiplier c hc hcc) c
    (fun _ => rfl) u x

/-- Squared-norm comparison: `x² ≤ C (a² + b²)` gives `x ≤ √C (a + b)`. -/
private theorem le_sqrt_mul_add_of_sq_le {x C a b : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : x ^ 2 ≤ C * (a ^ 2 + b ^ 2)) :
    x ≤ Real.sqrt C * (a + b) := by
  have htarget : 0 ≤ Real.sqrt C * (a + b) :=
    mul_nonneg (Real.sqrt_nonneg C) (add_nonneg ha hb)
  have hroot : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC
  have hsum : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by
    nlinarith [mul_nonneg ha hb]
  have htargetSq : C * (a ^ 2 + b ^ 2) ≤ (Real.sqrt C * (a + b)) ^ 2 := by
    calc
      C * (a ^ 2 + b ^ 2) ≤ C * (a + b) ^ 2 :=
        mul_le_mul_of_nonneg_left hsum hC
      _ = (Real.sqrt C * (a + b)) ^ 2 := by rw [mul_pow, hroot]
  exact (sq_le_sq₀ hx htarget).mp (h.trans htargetSq)

/-- The proved estimate applied to the localized Bessel output
`A u = η' Λ^σ η₁ u`, in the shared Sobolev norm. -/
theorem c9_localized_bessel_estimate {k N : ℕ}
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
    (η₁ η' η₂ : SchwartzMap (Hormander.B.Carrier N) ℝ) (σ : ℝ)
    (hη'η₂ : cutoffPrecedes (η' : Hormander.B.Carrier N → ℝ)
      (η₂ : Hormander.B.Carrier N → ℝ))
    (hη₂K : tsupport (η₂ : Hormander.B.Carrier N → ℝ) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Hormander.B.TestFunction N,
      Hormander.B.sobolevNorm ((2 : ℝ) / 4 ^ s)
          (localizedBesselOperator η₁ η' σ u) ≤
        C * (Hormander.B.sobolevNorm 0
            (Hormander.C.diffusionOperator
              (Hormander.C.c9SchwartzVectorField X hX hXc)
              (Hormander.C.c9SchwartzMultiplier c hc hcc)
              (localizedBesselOperator η₁ η' σ u)) +
          Hormander.B.sobolevNorm 0 (localizedBesselOperator η₁ η' σ u)) := by
  have hC9 := Hormander.C.subelliptic_estimate_unconditional X c hX hXc hc hcc hK hU hKU s hs
    w hws hw
  obtain ⟨C₀, hC₀⟩ :=
    applyC9_to_localizedBesselOperator_of_subelliptic_estimate X c hX hXc hc hcc hK hU hKU s hs
      w hws hw hC9 η₁ η₂ η' σ hη'η₂ hη₂K
  refine ⟨Real.sqrt (max C₀ 0), Real.sqrt_nonneg _, fun u => ?_⟩
  have hmain := hC₀ u
  set v : Hormander.B.TestFunction N := localizedBesselOperator η₁ η' σ u with hv
  have hpoint :
      (∫ x, ‖(∑ i : Fin k, fderiv ℝ (fun y => fderiv ℝ (v : Hormander.B.Carrier N → ℂ) y
            (X i.succ y)) x (X i.succ x)) +
          fderiv ℝ (v : Hormander.B.Carrier N → ℂ) x (X 0 x) + (c x : ℂ) * v x‖ ^ 2) =
        sobolevNorm 0 (Hormander.C.diffusionOperator
          (Hormander.C.c9SchwartzVectorField X hX hXc)
          (Hormander.C.c9SchwartzMultiplier c hc hcc) v) ^ 2 := by
    rw [Hormander.C.sobolevNorm_zero_sq]
    unfold Hormander.C.normSq
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [c9_diffusionOperator_apply X c hX hXc hc hcc v x]
  have hL2 : (∫ x, ‖v x‖ ^ 2) = sobolevNorm 0 v ^ 2 := by
    rw [Hormander.C.sobolevNorm_zero_sq]
    rfl
  have hfourier : (∫ ξ, (1 + ‖ξ‖ ^ 2) ^ ((2 : ℝ) / 4 ^ s) *
      ‖𝓕 (v : Hormander.B.Carrier N → ℂ) ξ‖ ^ 2) =
        sobolevNorm ((2 : ℝ) / 4 ^ s) v ^ 2 :=
    c9_weighted_fourier_eq_shared_sobolev_norm_sq ((2 : ℝ) / 4 ^ s) v
  rw [hfourier, hpoint, hL2] at hmain
  have hnonneg : 0 ≤ sobolevNorm 0 (Hormander.C.diffusionOperator
          (Hormander.C.c9SchwartzVectorField X hX hXc)
          (Hormander.C.c9SchwartzMultiplier c hc hcc) v) ^ 2 + sobolevNorm 0 v ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmax : sobolevNorm ((2 : ℝ) / 4 ^ s) v ^ 2 ≤ max C₀ 0 *
      (sobolevNorm 0 (Hormander.C.diffusionOperator
          (Hormander.C.c9SchwartzVectorField X hX hXc)
          (Hormander.C.c9SchwartzMultiplier c hc hcc) v) ^ 2 + sobolevNorm 0 v ^ 2) :=
    hmain.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hnonneg)
  exact le_sqrt_mul_add_of_sq_le (sobolevNorm_nonneg _ _) (le_max_right _ _)
    (sobolevNorm_nonneg _ _) (sobolevNorm_nonneg _ _) hmax

/-- The localized Bessel gain: the `H^{2/4^s}` norm of `A u = η' Λ^σ η₁ u` is bounded by
the localized data `‖η₂ L u‖_σ`, the commutator `‖[L, A] u‖₀` and `‖η₂ u‖_σ`. -/
theorem localized_bessel_gain_bound {k N : ℕ}
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
    (η₁ η' η₂ : SchwartzMap (Hormander.B.Carrier N) ℝ) (σ : ℝ)
    (hη₁η' : cutoffPrecedes (η₁ : Hormander.B.Carrier N → ℝ)
      (η' : Hormander.B.Carrier N → ℝ))
    (hη'η₂ : cutoffPrecedes (η' : Hormander.B.Carrier N → ℝ)
      (η₂ : Hormander.B.Carrier N → ℝ))
    (hη₂K : tsupport (η₂ : Hormander.B.Carrier N → ℝ) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Hormander.B.TestFunction N,
      Hormander.B.sobolevNorm ((2 : ℝ) / 4 ^ s)
          (localizedBesselOperator η₁ η' σ u) ≤
        C * (Hormander.B.sobolevNorm σ
            (Hormander.B.realMultiplierOperator η₂
              (Hormander.C.diffusionOperator
                (Hormander.C.c9SchwartzVectorField X hX hXc)
                (Hormander.C.c9SchwartzMultiplier c hc hcc) u)) +
          Hormander.B.sobolevNorm 0
            (Hormander.B.operatorComm
              (Hormander.C.diffusionOperator
                (Hormander.C.c9SchwartzVectorField X hX hXc)
                (Hormander.C.c9SchwartzMultiplier c hc hcc))
              (localizedBesselOperator η₁ η' σ) u) +
          Hormander.B.sobolevNorm σ (Hormander.B.realMultiplierOperator η₂ u)) := by
  obtain ⟨C₀, hC₀nn, hC₀⟩ :=
    c9_localized_bessel_estimate X c hX hXc hc hcc hK hU hKU s hs w hws hw η₁ η' η₂ σ hη'η₂ hη₂K
  obtain ⟨C₁, hC₁⟩ := localizedBesselOperator_l2_bound η₁ η' η₂ σ
    (cutoffPrecedes.trans hη₁η' hη'η₂)
  set L : Operator N := Hormander.C.diffusionOperator
    (Hormander.C.c9SchwartzVectorField X hX hXc)
    (Hormander.C.c9SchwartzMultiplier c hc hcc) with hL
  set A : Operator N := localizedBesselOperator η₁ η' σ with hA
  set m : ℝ := max (C₁ : ℝ) 1 with hm
  have hm1 : (1 : ℝ) ≤ m := le_max_right _ _
  have hm0 : (0 : ℝ) ≤ m := zero_le_one.trans hm1
  have hC₁m : (C₁ : ℝ) ≤ m := le_max_left _ _
  refine ⟨C₀ * m, mul_nonneg hC₀nn hm0, fun u => ?_⟩
  have hLA : L (A u) = A (L u) + operatorComm L A u := by
    simp [operatorComm]
  have hmain := hC₀ u
  have ha : sobolevNorm 0 (L (A u)) ≤
      m * sobolevNorm σ (realMultiplierOperator η₂ (L u)) +
        sobolevNorm 0 (operatorComm L A u) := by
    rw [hLA]
    refine (sobolevNorm_add_le 0 _ _).trans (add_le_add ?_ le_rfl)
    exact (hC₁ (L u)).trans
      (mul_le_mul_of_nonneg_right hC₁m (sobolevNorm_nonneg _ _))
  have hb : sobolevNorm 0 (A u) ≤ m * sobolevNorm σ (realMultiplierOperator η₂ u) :=
    (hC₁ u).trans (mul_le_mul_of_nonneg_right hC₁m (sobolevNorm_nonneg _ _))
  have hcomm : sobolevNorm 0 (operatorComm L A u) ≤ m * sobolevNorm 0 (operatorComm L A u) :=
    le_mul_of_one_le_left (sobolevNorm_nonneg _ _) hm1
  calc
    sobolevNorm ((2 : ℝ) / 4 ^ s) (A u) ≤
        C₀ * (sobolevNorm 0 (L (A u)) + sobolevNorm 0 (A u)) := hmain
    _ ≤ C₀ * (m * (sobolevNorm σ (realMultiplierOperator η₂ (L u)) +
        sobolevNorm 0 (operatorComm L A u) +
          sobolevNorm σ (realMultiplierOperator η₂ u))) := by
      refine mul_le_mul_of_nonneg_left ?_ hC₀nn
      nlinarith [ha, hb, hcomm]
    _ = C₀ * m * (sobolevNorm σ (realMultiplierOperator η₂ (L u)) +
        sobolevNorm 0 (operatorComm L A u) +
          sobolevNorm σ (realMultiplierOperator η₂ u)) := by ring

end Hormander.D

end

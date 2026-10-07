-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.OneStepFinal.Final

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap

namespace Hormander.E
open Hormander.B

variable {N : ℕ}

/-- Cutoffs absorb: `ψ (τ u) = τ u` if `ψ = 1` on the support of `τ`. -/
theorem cutoffDistr_absorb (τ ψ : SchwartzMap (Carrier N) ℝ)
    (h : ∀ x ∈ tsupport (τ : Carrier N → ℝ), ψ x = 1) (u : Tempered N) :
    cutoffDistr ψ (cutoffDistr τ u) = cutoffDistr τ u := by
  ext φ
  rw [cutoffDistr_apply_apply, cutoffDistr_apply_apply, cutoffDistr_apply_apply]
  have := LinearMap.congr_fun (mult_absorb τ ψ h) φ
  simp only [LinearMap.comp_apply] at this
  rw [this]

theorem cutoffDistr_comm (τ ψ : SchwartzMap (Carrier N) ℝ) (u : Tempered N) :
    cutoffDistr ψ (cutoffDistr τ u) = cutoffDistr τ (cutoffDistr ψ u) := by
  ext φ
  rw [cutoffDistr_apply_apply, cutoffDistr_apply_apply, cutoffDistr_apply_apply,
    cutoffDistr_apply_apply]
  have := LinearMap.congr_fun (realMult_comm τ ψ) φ
  simp only [LinearMap.comp_apply] at this
  rw [this]

theorem Eop_bOp (η₁ : SchwartzMap (Carrier N) ℝ) (δ : ℝ) (hδ : 0 < δ) (u : Tempered N) :
    Eop (bOp η₁ δ hδ) u = Hormander.A.Sδ N δ hδ (cutoffDistr η₁ u) := by
  unfold bOp
  rw [Eop_comp (hct_mollOp δ hδ) (hct_realMult η₁), ContinuousLinearMap.comp_apply,
    Eop_realMult, Eop_mollOp]


/-- The one-step regularization estimate follows from the localized gain estimate and the
mollifier converse. -/
theorem one_step_regularization_of_D1 {k N : ℕ}
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
    (hη : Hormander.D.cutoffPrecedes (η₁ : Hormander.B.Carrier N → ℝ)
      (η₂ : Hormander.B.Carrier N → ℝ))
    (hη₂K : tsupport (η₂ : Hormander.B.Carrier N → ℝ) ⊆ K)
    (r : ℝ) (hA6 : MollifierConverse N) (hD1 : D1Hypothesis) :
    ∃ C : ℝ, ∀ (u : 𝓢'(Hormander.B.Carrier N, ℂ))
      (a b : Hormander.A.SobolevSpace N r),
      a.toDistr = Hormander.B.cutoffDistr η₂ u →
      b.toDistr = Hormander.B.cutoffDistr η₂ (Hormander.hormanderOp X c u) →
      ∃ v : Hormander.A.SobolevSpace N (r + (2 : ℝ) / 4 ^ s),
        v.toDistr = Hormander.B.cutoffDistr η₁ u ∧ ‖v‖ ≤ C * (‖b‖ + ‖a‖) := by
  obtain ⟨χ, θ, ρ, hχ1, hχ2, h₂, h₃⟩ := exists_schwartz_chain hη
  have h₁ : Hormander.D.cutoffPrecedes (η₁ : Carrier N → ℝ) (θ : Carrier N → ℝ) :=
    Hormander.D.cutoffPrecedes.trans hχ1 hχ2
  have hρK : tsupport (ρ : Carrier N → ℝ) ⊆ K :=
    (cutoffPrecedes_tsupport_subset h₃).trans hη₂K
  have hη₁η : ∀ x ∈ tsupport (η₁ : Carrier N → ℝ), η₂ x = 1 :=
    plateau_of_precedes hη
  obtain ⟨CD, hCD⟩ := hD1 X c hX hXc hc hcc hK hU hKU s hs w hws hw θ ρ h₂ hρK r
  obtain ⟨CL, hCL0, hCL⟩ := Lz_bound (Hormander.C.c9SchwartzVectorField X hX hXc)
    (Hormander.C.c9SchwartzMultiplier c hc hcc) η₁ θ ρ η₂ h₁ h₂ h₃ hA6 r
  obtain ⟨C0, hC00, hC0⟩ := bdd_bOp η₁ η₂ hη₁η r
  obtain ⟨δ₀, hδ₀, hδ₀p⟩ := exists_mollifier_radius hχ2
  set CD' : ℝ := max CD 0 with hCD'
  have hCD'0 : 0 ≤ CD' := le_max_right _ _
  refine ⟨CD' * (CL + C0), fun u a b ha hb => ?_⟩
  set M := ‖b‖ + ‖a‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have hb' : b.toDistr = cutoffDistr η₂ (Eop (Hormander.C.diffusionOperator
      (Hormander.C.c9SchwartzVectorField X hX hXc)
      (Hormander.C.c9SchwartzMultiplier c hc hcc)) u) := by
    rw [hb, Eop_diffusion_eq X c hX hXc hc hcc]
  -- the localization `η₁ u` lies in `H^r`
  have hmem : TemperedDistribution.MemSobolev r 2 (cutoffDistr η₁ u) := by
    have e : cutoffDistr η₁ u = cutoffDistr η₁ a.toDistr := by
      rw [ha, cutoffDistr_comm, cutoffDistr_absorb η₁ η₂ hη₁η]
    have hM' : HasOrder 0 (realMultiplierOperator η₁) :=
      hasOrder_multiplierOperator_zero (complexifyRealSchwartz η₁)
    obtain ⟨C', hC'⟩ := hM' r
    obtain ⟨v, hv, -⟩ := Eop_bdd_global (hct_realMult η₁) (m := 0) (s := r) (r' := r) (by simp)
      (C := C') (fun φ => by simpa using hC' φ) a
    rw [e]
    exact Bdd.of_memSobolev v (by rw [hv, Eop_realMult])
  have hτ : cutoffDistr χ (cutoffDistr η₁ u) = cutoffDistr η₁ u :=
    cutoffDistr_absorb η₁ χ (plateau_of_precedes hχ1) u
  refine hA6 (r + (2 : ℝ) / 4 ^ s) (cutoffDistr η₁ u) (CD' * (CL + C0) * M) δ₀ hδ₀
    (fun δ hδ hδlt => ?_)
  have hψ : ∀ x ∈ tsupport (χ : Carrier N → ℝ), ∀ y, ‖x - y‖ ≤ δ / 2 → θ y = 1 :=
    fun x hx y hy => hδ₀p x hx y (hy.trans (by linarith))
  obtain ⟨g, hg⟩ := exists_testFunction_Sδ χ θ hχ2.2.2.2.1 (cutoffDistr η₁ u) hmem hτ δ hδ hψ
  have hθfix := cutoffDistr_Sδ_fix χ θ (cutoffDistr η₁ u) hτ δ hδ hψ
  have hgB : (g : Tempered N) = Eop (bOp η₁ δ hδ) u := by rw [hg, Eop_bOp]
  have hθg : realMultiplierOperator θ g = g := by
    apply testToTempered_injective'
    rw [← Eop_test (hct_realMult θ), Eop_realMult, hg, hθfix]
  have hθρ := plateau_of_precedes h₂
  have hρg : realMultiplierOperator ρ g = g := by
    apply realMult_eq_self_of_tsupport
    intro x hx
    apply hθρ
    have := tsupport_realMult_subset θ g
    rw [hθg] at this
    exact this hx
  have hρLg : realMultiplierOperator ρ (Hormander.C.diffusionOperator
      (Hormander.C.c9SchwartzVectorField X hX hXc)
      (Hormander.C.c9SchwartzMultiplier c hc hcc) g) =
      Hormander.C.diffusionOperator (Hormander.C.c9SchwartzVectorField X hX hXc)
      (Hormander.C.c9SchwartzMultiplier c hc hcc) g := by
    apply realMult_eq_self_of_tsupport
    intro x hx
    apply hθρ
    have hsub : tsupport (Hormander.C.diffusionOperator (Hormander.C.c9SchwartzVectorField X hX hXc)
        (Hormander.C.c9SchwartzMultiplier c hc hcc) g : Carrier N → ℂ) ⊆
        tsupport (g : Carrier N → ℂ) := by
      apply closure_minimal _ (isClosed_tsupport _)
      intro y hy
      by_contra hyg
      exact hy (diffusion_apply_eq_zero _ _ g y hyg)
    have := tsupport_realMult_subset θ g
    rw [hθg] at this
    exact this (hsub hx)
  -- bounds
  have hBL := hCL ⟨δ, hδ⟩ u a b ha hb'
  have hBB := hC0 ⟨δ, hδ⟩ u a ha
  have hnL : sobolevNorm r (Hormander.C.diffusionOperator
      (Hormander.C.c9SchwartzVectorField X hX hXc)
      (Hormander.C.c9SchwartzMultiplier c hc hcc) g) ≤ CL * M := by
    have h1 : Bdd r ((Hormander.C.diffusionOperator (Hormander.C.c9SchwartzVectorField X hX hXc)
        (Hormander.C.c9SchwartzMultiplier c hc hcc) g : TestFunction N) : Tempered N)
        (CL * (‖a‖ + ‖b‖)) := by
      rw [← Eop_test (hct_diffusion _ _), hgB]
      exact hBL
    have := h1.test_le
    rwa [add_comm ‖a‖ ‖b‖] at this
  have hng : sobolevNorm r g ≤ C0 * ‖a‖ := by
    have h1 : Bdd r (g : Tempered N) (C0 * ‖a‖) := by rw [hgB]; exact hBB
    exact h1.test_le
  have hD := hCD g
  rw [hθg, hρg, hρLg] at hD
  have hD' : sobolevNorm (r + (2 : ℝ) / 4 ^ s) g ≤ CD' * (CL * M + C0 * M) := by
    have hle : CD * (sobolevNorm r (Hormander.C.diffusionOperator
        (Hormander.C.c9SchwartzVectorField X hX hXc)
        (Hormander.C.c9SchwartzMultiplier c hc hcc) g) + sobolevNorm r g) ≤
        CD' * (CL * M + C0 * M) := by
      have hsum0 : 0 ≤ sobolevNorm r (Hormander.C.diffusionOperator
        (Hormander.C.c9SchwartzVectorField X hX hXc)
        (Hormander.C.c9SchwartzMultiplier c hc hcc) g) + sobolevNorm r g :=
        add_nonneg (sobolevNorm_nonneg _ _) (sobolevNorm_nonneg _ _)
      calc _ ≤ CD' * (sobolevNorm r (Hormander.C.diffusionOperator
          (Hormander.C.c9SchwartzVectorField X hX hXc)
          (Hormander.C.c9SchwartzMultiplier c hc hcc) g) + sobolevNorm r g) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hsum0
        _ ≤ CD' * (CL * M + C0 * M) := by
            apply mul_le_mul_of_nonneg_left _ hCD'0
            have : C0 * ‖a‖ ≤ C0 * M := by gcongr; linarith [norm_nonneg b]
            linarith
    exact hD.trans hle
  have hfin : Bdd (r + (2 : ℝ) / 4 ^ s) (g : Tempered N) (CD' * (CL + C0) * M) :=
    (Bdd.of_test _ g).mono (by nlinarith)
  rw [hg] at hfin
  exact hfin

end Hormander.E

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.BudgetedGeneratorDerivative

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G4

/-- Explicit finite-jet multiplier for one expansion derivative. -/
def expansionDerivativeBudget (n p h a : ℕ) (P A : ℝ) : ℝ :=
  2 ^ h * P + scalarJetMultiplier h * (a : ℝ) * ((p : ℝ) * ((n : ℝ) + 1) * A)

/-- The derivative multiplier is nonnegative for nonnegative input budgets. -/
theorem expansionDerivativeBudget_nonneg (n p h a : ℕ) {P A : ℝ}
    (hP : 0 ≤ P) (hA : 0 ≤ A) : 0 ≤ expansionDerivativeBudget n p h a P A := by
  unfold expansionDerivativeBudget
  have hs := scalarJetMultiplier_nonneg h
  positivity

/-- Actual differentiation propagates the explicit coefficient
budget, consumes one jet, adds at most one generator factor, and loses
exactly the differentiating field's signed weight. -/
theorem budgetedExpansion_derivative {k n s : ℕ}
    {Ω K₀ : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hKΩ : K₀ ⊆ Ω)
    {w : Fin (k + 1) → ℕ+} {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (B : Fin n → ShortWord w s)
    (L : ShortWord w s) {a h : ℕ} {p : ℤ} {f : (Fin n → ℝ) → ℝ} {C P A : ℝ}
    (hP : 0 ≤ P) (hA : 0 ≤ A)
    (hZP : HasJetBound Ω K₀ (shortField w X L) h P)
    (hjets : ∀ L J K : ShortWord w s,
      HasJetBound Ω K₀ (shortBracketCoefficient w X L J K) h A)
    (hf : HasBudgetedGeneratorExpansion Ω K₀ (shortField w X) (shortWeight w) B a p (h + 1) f C) :
    HasBudgetedGeneratorExpansion Ω K₀ (shortField w X) (shortWeight w) B (a + 1)
      (p - ((shortWeight w L : ℕ) : ℤ)) h (fieldDerivative (shortField w X L) f)
      (C * expansionDerivativeBudget n (Fintype.card (ShortWord w s)) h a P A) := by
  let Z := shortField (s := s) w X
  let v := shortWeight (s := s) w
  have hZ : ∀ J : ShortWord w s, ContDiffOn ℝ (⊤ : ℕ∞) (Z J) Ω := shortField_contDiffOn hΩ hX
  have hnear : ∀ x ∈ Ω ∩ {x | frameDet Z B x ≠ 0},
      Ω ∩ {y | frameDet Z B y ≠ 0} ∈ 𝓝 x := by
    intro x hx
    apply inter_mem (hΩ.mem_nhds hx.1)
    exact ((frameDet_contDiffOn hZ B).contDiffAt (hΩ.mem_nhds hx.1)).continuousAt.preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds hx.2)
  induction hf with
  | zero =>
    simpa only [zero_mul] using (HasBudgetedGeneratorExpansion.zero.congr
      (g := fieldDerivative (Z L) (fun _ => 0)) (fun x _ => by simp [fieldDerivative]))
  | term d g C hC hd hdC hg =>
    have hd' : ContDiffOn ℝ (⊤ : ℕ∞) (fieldDerivative (Z L) d) Ω :=
      (hd.fderiv_of_isOpen hΩ (by simp)).clm_apply (hZ L)
    have hjd := hZP.fieldDerivative hΩ hKΩ (hZ L) hd hP hC hdC
    have hweight : p - ((v L : ℕ) : ℤ) ≤ p := by
      have hv : 0 ≤ ((v L : ℕ) : ℤ) := by positivity
      omega
    have hfirst := budgetedExpansion_mono (Nat.le_succ a) hweight le_rfl
      (HasBudgetedGeneratorExpansion.term (fieldDerivative (Z L) d) g _
        (by positivity) hd' hjd hg)
    have hsecond := budgetedExpansion_smooth_mul hΩ hKΩ hd hC
      (hdC.mono (Nat.le_succ h)) (generator_derivative_budget hΩ hKΩ hX hstep B L hA hjets hg)
    have hgs := generatorExpansion_contDiffOn hZ (generator_expansion (Ω := Ω) hg)
    have hb := (HasBudgetedGeneratorExpansion.add hfirst hsecond).congr
      (g := fieldDerivative (Z L) (fun x => d x * g x)) (fun x hx =>
        S.fieldDerivative_mul (Z L) d g x
          ((hd.contDiffAt (hΩ.mem_nhds hx.1)).differentiableAt (by simp))
          ((hgs.contDiffAt (hnear x hx)).differentiableAt (by simp)))
    convert hb using 1
    unfold expansionDerivativeBudget
    ring
  | @add f g C D hf hg ihf ihg =>
    have hfs := generatorExpansion_contDiffOn hZ (budgetedGeneratorExpansion_forget hf)
    have hgs := generatorExpansion_contDiffOn hZ (budgetedGeneratorExpansion_forget hg)
    have hb := (HasBudgetedGeneratorExpansion.add ihf ihg).congr
      (g := fieldDerivative (Z L) (fun x => f x + g x)) (fun x hx => by
        simp only [fieldDerivative, fderiv_fun_add
          ((hfs.contDiffAt (hnear x hx)).differentiableAt (by simp))
          ((hgs.contDiffAt (hnear x hx)).differentiableAt (by simp)), add_apply]
        rfl)
    convert hb using 1
    ring
  | enlarge hf hCD ih => exact ih.enlarge (mul_le_mul_of_nonneg_right hCD
      (expansionDerivativeBudget_nonneg n _ h a hP hA))
  | @congr f₁ g₁ C hf heq ih =>
    exact ih.congr (fun x hx => by
      have he : g₁ =ᶠ[𝓝 x] f₁ := by
        filter_upwards [hnear x hx] with y hy
        exact heq hy
      exact congrArg (fun D => D (Z L x)) (he.fderiv_eq (𝕜 := ℝ)))

end RothschildStein.G4

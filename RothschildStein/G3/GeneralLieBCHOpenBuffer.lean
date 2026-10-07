-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.GeneralLieBCHPointError
public import RothschildStein.G3.DilatedLieCurveTravel
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.G3

/-- The numerical BCH error on an open buffer needs no separate compact
trajectory set: the same primitive jets bound every trajectory's travel. -/
theorem generalLie_BCH_point_error_on_open_buffer {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (f g : formalSpan a s p) (δ : ℝ) (hs : 1 ≤ s)
    (α β γ : ℝ → (Fin N → ℝ))
    (hα : ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt α
      (finiteLieField D X ⟨finiteDilate δ f.val,finiteDilate_mem_formalSpan δ f.property⟩ (α t)) t)
    (hβ : ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt β
      (finiteLieField D X ⟨finiteDilate δ g.val,finiteDilate_mem_formalSpan δ g.property⟩ (β t)) t)
    (hγ : ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt γ
      (finiteLieField D X ⟨finiteDilate δ (modelProduct f g).val,
        finiteDilate_mem_formalSpan δ (modelProduct f g).property⟩ (γ t)) t)
    (hαΩ : ∀ t ∈ Ioo (-2 : ℝ) 2, α t ∈ Ω)
    (hβΩ : ∀ t ∈ Ioo (-2 : ℝ) 2, β t ∈ Ω)
    (hγΩ : ∀ t ∈ Ioo (-2 : ℝ) 2, γ t ∈ Ω)
    (hβ₀ : β 0 = α 1) (hγ₀ : γ 0 = α 0)
    {B : ℝ} (hB : 0 ≤ B) (hδ : |δ| ≤ 1)
    (hjets : ∀ x ∈ Ω, ∀ i k, k ≤ 3*s+2 → ‖iteratedFDeriv ℝ k (X i) x‖ ≤ B) :
    ‖β 1-γ 1‖ ≤ |δ|^(s+1)*generalLieBCHErrorCoefficient D f g
      (primitiveWordJetBudget D (3*s+2) B)
      (max (generalLieTravelBudget D f B + generalLieTravelBudget D g B +
        generalLieTravelBudget D (modelProduct f g) B) 1) := by
  let A := generalLieTravelBudget D f B
  let C := generalLieTravelBudget D g B
  let H := generalLieTravelBudget D (modelProduct f g) B
  have hA : 0 ≤ A := generalLieTravelBudget_nonneg D f hB
  have hC : 0 ≤ C := generalLieTravelBudget_nonneg D g hB
  have hH : 0 ≤ H := generalLieTravelBudget_nonneg D (modelProduct f g) hB
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioo (-2 : ℝ) 2 := by
    intro t ht; constructor <;> linarith [ht.1,ht.2]
  have ha : ∀ t ∈ Icc (0 : ℝ) 1, ‖α t-α 0‖ ≤ A := by
    intro t ht
    have he := dilatedLieCurve_displacement_le D Ω X hX f δ hB hδ α hα hαΩ hjets (hseg t ht)
    have habs : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    calc
      _ ≤ |δ| * A * |t| := he
      _ ≤ 1 * A * 1 := mul_le_mul (mul_le_mul_of_nonneg_right hδ hA) habs
        (abs_nonneg t) (by positivity)
      _ = A := by ring
  have hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖β t-β 0‖ ≤ C := by
    intro t ht
    have he := dilatedLieCurve_displacement_le D Ω X hX g δ hB hδ β hβ hβΩ hjets (hseg t ht)
    have habs : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    calc
      _ ≤ |δ| * C * |t| := he
      _ ≤ 1 * C * 1 := mul_le_mul (mul_le_mul_of_nonneg_right hδ hC) habs
        (abs_nonneg t) (by positivity)
      _ = C := by ring
  have hc : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t-γ 0‖ ≤ H := by
    intro t ht
    have he := dilatedLieCurve_displacement_le D Ω X hX (modelProduct f g) δ hB hδ γ hγ hγΩ hjets (hseg t ht)
    have habs : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    calc
      _ ≤ |δ| * H * |t| := he
      _ ≤ 1 * H * 1 := mul_le_mul (mul_le_mul_of_nonneg_right hδ hH) habs
        (abs_nonneg t) (by positivity)
      _ = H := by ring
  let K : Set (Fin N → ℝ) := Ω ∩ Metric.closedBall (α 0) (A+C+H)
  apply generalLie_BCH_point_error_of_finite_primitive_jets D Ω X hX f g δ hs
    α β γ hα hβ hγ hαΩ hβΩ hγΩ hβ₀ hγ₀ (α 0)
    (K := K) (fun _ hx => hx.2) (fun _ hx => hx.1) hB hδ
  · intro t ht
    refine ⟨hαΩ t (hseg t ht),?_⟩
    change dist (α t) (α 0) ≤ A+C+H
    rw [dist_eq_norm]
    linarith [ha t ht]
  · intro t ht
    refine ⟨hβΩ t (hseg t ht),?_⟩
    change dist (β t) (α 0) ≤ A+C+H
    rw [dist_eq_norm]
    have he := norm_sub_le_norm_sub_add_norm_sub (β t) (β 0) (α 0)
    rw [hβ₀] at he
    have hb' := hb t ht
    rw [hβ₀] at hb'
    linarith [ha 1 (by simp)]
  · intro t ht
    refine ⟨hγΩ t (hseg t ht),?_⟩
    change dist (γ t) (α 0) ≤ A+C+H
    rw [dist_eq_norm]
    simpa only [hγ₀] using (hc t ht).trans (by linarith : H ≤ A+C+H)
  · intro i k hk x hx
    exact hjets x hx.1 i k hk
end RothschildStein.G3

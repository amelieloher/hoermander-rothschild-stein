-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.LinearParameterFieldJets
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G3

/-- Joint parameter and spatial jets of a finite coefficient field
have an explicit binomial bound (BB pp. 413–415). -/
theorem norm_finite_coefficient_field_jet_le {m : ℕ}
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set E} (hΩ : IsOpen Ω) (Y : Fin m → E → F)
    (hY : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Y j) Ω)
    {q : (Fin m → ℝ) × E} (hq : q.2 ∈ Ω)
    (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hYB : ∀ j k, k ≤ n → ‖iteratedFDeriv ℝ k (Y j) q.2‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun z : (Fin m → ℝ) × E => ∑ j, z.1 j • Y j z.2) q‖ ≤
      (m : ℝ) * 2 ^ n * max ‖q.1‖ 1 * B := by
  have hj : ∀ j, ContDiffAt ℝ n (fun z : (Fin m → ℝ) × E => z.1 j • Y j z.2) q := by
    intro j
    have hc : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : (Fin m → ℝ) × E => z.1 j) q :=
      by
        simpa only [Function.comp_def,ContinuousLinearMap.proj_apply] using
          (((ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ).contDiff.comp contDiff_fst).contDiffAt :
            ContDiffAt ℝ (⊤ : ℕ∞) ((ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ) ∘ Prod.fst) q)
    have hy : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : (Fin m → ℝ) × E => Y j z.2) q :=
      ((hY j).contDiffAt (hΩ.mem_nhds hq)).comp q contDiffAt_snd
    exact (hc.smul hy).of_le (by simp)
  rw [iteratedFDeriv_fun_sum_apply (fun j _ => hj j)]
  apply (norm_sum_le _ _).trans
  have hbound : ∀ j : Fin m,
      ‖iteratedFDeriv ℝ n (fun z : (Fin m → ℝ) × E => z.1 j • Y j z.2) q‖ ≤
        2 ^ n * max ‖q.1‖ 1 * B := by
    intro j
    let L : (Fin m → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
    have hL : ‖L‖ ≤ 1 := by
      apply L.opNorm_le_bound zero_le_one
      intro c
      change ‖c j‖ ≤ 1 * ‖c‖
      simpa only [one_mul] using norm_le_pi_norm c j
    exact norm_linear_parameter_field_jet_le hΩ L (Y j) (hY j) hq n
      ((norm_nonneg _).trans (le_max_left _ _)) hB
      ((norm_le_pi_norm q.1 j).trans (le_max_left _ _))
      (hL.trans (le_max_right _ _)) (hYB j)
  calc
    _ ≤ ∑ _ : Fin m, 2 ^ n * max ‖q.1‖ 1 * B :=
      Finset.sum_le_sum (fun j _ => hbound j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.PrimitiveRetainedEndpointBridge
public import RothschildStein.G3.DilatedCoefficientNorm
@[expose] public section
noncomputable section
open Set Metric
open scoped BigOperators
namespace RothschildStein.G3

/-- A single numerical rescaling works for every primitive generator. -/
theorem exists_primitive_rescaling_radius {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) {σ : ℝ} (hσ : 0 < σ) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
      ∀ i : Fin a, D.basis.equivFun (κ • (wordLieElement [i] : formalSpan a s p)) ∈ ball 0 σ := by
  let A := 1+∑ i : Fin a, ‖D.basis.equivFun (wordLieElement [i])‖
  have hA : 1 ≤ A := by dsimp only [A]; linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => norm_nonneg (D.basis.equivFun (wordLieElement [i])))]
  let κ := min 1 (σ/(4*A))
  have hκ : 0 < κ := lt_min zero_lt_one (by positivity)
  refine ⟨κ,hκ,min_le_left _ _,?_⟩
  intro i
  have hi : ‖D.basis.equivFun (wordLieElement [i])‖ ≤ A := by
    have he := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => norm_nonneg (D.basis.equivFun (wordLieElement [j]))) (Finset.mem_univ i)
    dsimp only [A]
    linarith
  have hsmall : κ*A ≤ σ/4 := by
    have he := (le_div_iff₀ (by positivity : 0 < 4*A)).mp (min_le_right 1 (σ/(4*A)))
    change κ*(4*A) ≤ σ at he
    nlinarith
  rw [mem_ball_zero_iff,map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hκ]
  exact (mul_le_mul_of_nonneg_left hi hκ.le).trans_lt (hsmall.trans_lt (by linarith))

theorem dilated_signed_primitive_mem_ball {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (b : Fin a × Bool) {κ σ t : ℝ}
    (hκ : 0 < κ) (htκ : |t| ≤ κ) (ht1 : |t| ≤ 1)
    (hc : D.basis.equivFun (κ • (wordLieElement [b.1] : formalSpan a s p)) ∈ ball 0 σ) :
    dilatedInputCoordinates D (primitiveScheduleLieInput b) t ∈ ball 0 σ := by
  have he : ‖D.basis.equivFun (primitiveScheduleLieInput b)‖ =
      ‖D.basis.equivFun (wordLieElement [b.1])‖ := by
    rcases b with ⟨i,b⟩
    cases b <;> simp [primitiveScheduleLieInput]
  have hb := (norm_dilatedInputCoordinates_le D (primitiveScheduleLieInput b) ht1).trans
    (mul_le_mul_of_nonneg_right htκ (norm_nonneg _))
  rw [he] at hb
  rw [mem_ball_zero_iff,map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hκ] at hc
  exact mem_ball_zero_iff.mpr (hb.trans_lt hc)
end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.LinearCoefficientJets
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G3

theorem norm_linear_parameter_field_jet_le
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set E} (hΩ : IsOpen Ω) (L : P →L[ℝ] ℝ) (Y : E → F)
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y Ω) {q : P × E} (hq : q.2 ∈ Ω)
    (n : ℕ) {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hLA : ‖L q.1‖ ≤ A) (hLn : ‖L‖ ≤ A)
    (hYB : ∀ k ≤ n, ‖iteratedFDeriv ℝ k Y q.2‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun z : P × E => L z.1 • Y z.2) q‖ ≤
      2 ^ n * A * B := by
  let S : Set (P × E) := Prod.snd ⁻¹' Ω
  have hS : IsOpen S := hΩ.preimage continuous_snd
  have hqS : q ∈ S := hq
  let C := L.comp (ContinuousLinearMap.fst ℝ P E)
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : P × E => L z.1) S := C.contDiff.contDiffOn
  have hy : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : P × E => Y z.2) S :=
    hY.comp contDiffOn_snd (fun _ hz => hz)
  have hh := norm_iteratedFDerivWithin_smul_le hc hy hS.uniqueDiffOn hqS (n := n) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hS hqS] at hh
  apply hh.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hC : ‖C‖ ≤ A :=
        C.opNorm_le_bound hA (fun z => by
          change ‖L z.1‖ ≤ A * ‖z‖
          exact (L.le_opNorm z.1).trans
            ((mul_le_mul_of_nonneg_right hLn (norm_nonneg _)).trans
              (mul_le_mul_of_nonneg_left (norm_fst_le z) hA)))
      have ha : ‖iteratedFDeriv ℝ i (fun z : P × E => L z.1) q‖ ≤ A :=
        (norm_linear_coefficient_jet_le C q i).trans (max_le hLA hC)
      have hb : ‖iteratedFDeriv ℝ (n-i) (fun z : P × E => Y z.2) q‖ ≤ B :=
        (norm_snd_pullback_jet_le hΩ hY (n-i) q hq).trans (hYB (n-i) (by omega))
      gcongr
    _ = _ := by
      simp_rw [← Finset.sum_mul,← Nat.cast_sum,Nat.sum_range_choose]
      push_cast
      rfl
end RothschildStein.G3

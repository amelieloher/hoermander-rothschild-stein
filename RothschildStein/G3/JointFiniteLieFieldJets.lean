-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteCoefficientFieldJets
public import RothschildStein.G3.BasisWordUniformJets
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- Explicit mixed coefficient-field jets in terms of finitely many
primitive coefficient jets; the word budget uses ordinary length (BB pp. 413–415). -/
theorem norm_joint_finiteLie_field_jet_le {a s N R : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (q : (Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) (hq : q.2 ∈ Ω)
    {B : ℝ} (hB : 0 ≤ B)
    (hXjet : ∀ i j, j ≤ R → ‖iteratedFDeriv ℝ j (X i) q.2‖ ≤ B)
    (n : ℕ) (hn : n+s ≤ R+1) :
    ‖iteratedFDeriv ℝ n
      (fun z : (Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ) =>
        ∑ j, z.1 j • wordBracket X (modelBasisWord D j) z.2) q‖ ≤
      (freeDimension a s p : ℝ) * 2 ^ n * max ‖q.1‖ 1 *
        (∑ j, (2 ^ (R+1)) ^ ((modelBasisWord D j).length-1) * B ^ (modelBasisWord D j).length) := by
  apply norm_finite_coefficient_field_jet_le Ω.isOpen
    (fun j => wordBracket X (modelBasisWord D j))
    (fun j => G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D j)) hq n
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (pow_nonneg hB _))
  · intro j k hk
    exact norm_basisWord_jet_le_uniform_sum D Ω X hX hq hB hXjet k (by omega) j
end RothschildStein.G3

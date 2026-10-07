-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteLieFieldDilation
public import RothschildStein.G3.WordBracketJetBounds
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- A single finite polynomial constant bounds every retained
bracket-field jet, preserving the ordinary jet budget of products in the
bracket alphabet (BB Lemma 9.22, pp. 413–414). -/
theorem norm_basisWord_jet_le_uniform_sum {a s N R : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) {B : ℝ} (hB : 0 ≤ B)
    (hXjet : ∀ i, ∀ j ≤ R, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ B)
    (r : ℕ) (hr : r + s ≤ R + 1) (j : Fin (freeDimension a s p)) :
    ‖iteratedFDeriv ℝ r (wordBracket X (modelBasisWord D j)) x‖ ≤
      ∑ l, (2 ^ (R + 1)) ^ ((modelBasisWord D l).length - 1) * B ^ (modelBasisWord D l).length := by
  have hj := modelBasisWord_spec D j
  have hl : (modelBasisWord D j).length ≤ s := (length_le_weight p _).trans hj.2.1
  apply (norm_wordBracket_jet_le Ω X hX hx hB hXjet (modelBasisWord D j) hj.1 r (by omega)).trans
  exact Finset.single_le_sum
    (fun l _ => show 0 ≤ (2 ^ (R + 1) : ℝ) ^ ((modelBasisWord D l).length - 1) * B ^ (modelBasisWord D l).length from mul_nonneg (by positivity) (pow_nonneg hB _)) (Finset.mem_univ j)
end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.WeightedWordScaling
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.G3

/-- Weighted primitive scaling preserves the full parameter
weight in each spatial jet; the jet loss is the ordinary word length. -/
theorem norm_weighted_wordDerivative_jet_le {a N R : ℕ}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (p : Fin a → ℕ+) (δ : ℝ) (I : List (Fin a))
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) {B F : ℝ} (hB : 0 ≤ B)
    (hXjet : ∀ i, ∀ j ≤ R, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ B)
    (hfjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j f x‖ ≤ F)
    (n : ℕ) (hn : n + I.length ≤ R) :
    ‖iteratedFDeriv ℝ n (wordDerivative (fun i => δ ^ (p i : ℕ) • X i) I f) x‖ ≤
      |δ| ^ wordWeight p I * ((2 ^ R * B) ^ I.length * F) := by
  have he : wordDerivative (fun i => δ ^ (p i : ℕ) • X i) I f =ᶠ[𝓝 x]
      δ ^ wordWeight p I • wordDerivative X I f := by
    filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    exact wordDerivative_weighted_scale Ω X hX p δ I f hf hy
  have hfn : ContDiffAt ℝ n (wordDerivative X I f) x :=
    ((S.contDiffOn_wordDerivative Ω X hX I f hf).contDiffAt
      (Ω.isOpen.mem_nhds hx)).of_le (by simp)
  rw [(he.iteratedFDeriv ℝ n).eq_of_nhds,
    iteratedFDeriv_const_smul_apply hfn, norm_smul, Real.norm_eq_abs, abs_pow]
  exact mul_le_mul_of_nonneg_left
    (norm_wordDerivative_jet_le Ω X hX f hf hx hB hXjet hfjet I n hn)
    (pow_nonneg (abs_nonneg δ) _)
end RothschildStein.G3

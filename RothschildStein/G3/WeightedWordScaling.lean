-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.WordDerivativeBounds
public import RothschildStein.Definitions.wordWeight
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.G3

/-- Weighted primitive times contribute exactly the sum of
letter weights to every ordered differential word (BB pp. 417–420). -/
theorem wordDerivative_weighted_scale {a N : ℕ} (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (p : Fin a → ℕ+) (δ : ℝ) (I : List (Fin a))
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) :
    wordDerivative (fun i => δ ^ (p i : ℕ) • X i) I f x =
      δ ^ wordWeight p I * wordDerivative X I f x := by
  induction I generalizing x with
  | nil => simp [wordDerivative, wordWeight]
  | cons i I ih =>
    have he : wordDerivative (fun j => δ ^ (p j : ℕ) • X j) I f =ᶠ[𝓝 x]
        (fun y => δ ^ wordWeight p I • wordDerivative X I f y) := by
      filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
      exact ih hy
    change (fderiv ℝ _ x) ((δ ^ (p i : ℕ) • X i) x) = _
    rw [he.fderiv_eq, fderiv_fun_const_smul
      (((S.contDiffOn_wordDerivative Ω X hX I f hf).contDiffAt
        (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp))]
    simp only [Pi.smul_apply, smul_apply, map_smul, smul_eq_mul, wordDerivative,
      fieldDerivative, wordWeight, List.map_cons, List.sum_cons, pow_add]
    ring
end RothschildStein.G3

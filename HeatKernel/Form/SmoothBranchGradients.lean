-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ConstantDifferenceGradients
import Mathlib.Tactic.Linter

/-! # Horizontal chain rules on smooth scalar branches -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped NNReal

namespace HeatKernel

/-- An energy representative of a scalar composition obeys the smooth branch chain rule
wherever the scalar map agrees with a globally C¹ branch with bounded derivative. The branch
need not fix zero. -/
theorem energyGraph_gradient_eq_on_smooth_branch {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (u w : energyGraph (N := N) ⊤ X) {η ψ : ℝ → ℝ}
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => η ((u : GradientSpace (N := N) ⊤ q).fst x))
    (hψ : ContDiff ℝ 1 ψ) {C : ℝ≥0} (hb : ∀ s, ‖deriv ψ s‖ ≤ C) (i : Fin q) :
    ∀ᵐ x ∂volume, η ((u : GradientSpace (N := N) ⊤ q).fst x) =
      ψ ((u : GradientSpace (N := N) ⊤ q).fst x) →
      (w : GradientSpace (N := N) ⊤ q).snd i x =
        deriv ψ ((u : GradientSpace (N := N) ⊤ q).fst x) *
          (u : GradientSpace (N := N) ⊤ q).snd i x := by
  let f : ℝ → ℝ := fun s => ψ s - ψ 0
  have hf : ContDiff ℝ 1 f := hψ.sub contDiff_const
  have hf0 : f 0 = 0 := sub_self _
  have hd : ∀ s, deriv f s = deriv ψ s := fun s =>
    ((hψ.differentiable (by simp) s).hasDerivAt.sub_const (ψ 0)).deriv
  have hfb : ∀ s, ‖deriv f s‖ ≤ C := fun s => by rw [hd]; exact hb s
  obtain ⟨v, hvf, hvg⟩ := exists_energyGraph_comp_contDiff_one X hX u hf hf0 hfb
  filter_upwards [hw, hvf, hvg i,
    energyGraph_gradient_eq_on_constant_difference X hX w v (ψ 0) i] with x hwx hvx hgx hx he
  have hv : (w : GradientSpace (N := N) ⊤ q).fst x =
      (v : GradientSpace (N := N) ⊤ q).fst x + ψ 0 := by
    rw [hwx, hvx, he]
    dsimp only [f]
    ring
  rw [hx hv, hgx, hd]



end HeatKernel

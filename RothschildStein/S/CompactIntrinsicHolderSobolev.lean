-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntrinsicWeakHolderExport
public import RothschildStein.S.CompactWeakHolderSobolev
public import RothschildStein.Definitions.memHolderXCompact

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n q : ℕ} {p : ℝ≥0∞}

/-- The exact compact intrinsic Hölder class embeds
in the exact zero-boundary Sobolev class for every finite p
at least one (BB p. 593; Cor 2.10, p. 73). -/
theorem memSobolevXZero_of_memHolderXCompact
    [Fact (1 ≤ p)] (Ω U : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j,ContDiffOn ℝ (⊤ : ℕ∞) (X j) (U : Set (Fin n → ℝ)))
    (k : ℕ) {α : ℝ} (hα : 0 < α) (hpt : p ≠ ⊤)
    {f : (Fin n → ℝ) → ℝ} (hf : memHolderXCompact w X G.d U k α f) :
    memSobolevXZero w X U k p f := by
  exact memSobolevXZero_of_memWeakHolderX_compact Ω U G hU w X hX k hα hpt
    (memWeakHolderX_of_memHolderX Ω U G hU w X hX k hα hf.1) hf.2.1 hf.2.2 (by
      intro x hx
      by_contra hn
      exact hx.2 (subset_closure ⟨hx.1,hn⟩))

end RothschildStein.S

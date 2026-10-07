-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakGraph
public import RothschildStein.S.Conjugate
public import Mathlib.Analysis.Normed.Lp.PiLp
public import RothschildStein.S.SobolevAE
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.S
variable {n m : ℕ}
variable (w : Fin m → ℕ+) (Ω : Opens (Fin n → ℝ))
variable (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
variable (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
variable (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
include hX

omit [Fact (1 ≤ p)] in
/-- Smooth compact tests belong to every weighted Sobolev class
(BB Def. 2.2, p. 68; Prop. 2.5, p. 69). -/
theorem test_memSobolevX (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    memSobolevX w X Ω k p φ := by
  refine ⟨φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport, fun I _ => ?_⟩
  let ψ := wordDerivativeTest Ω X hX I φ
  exact ⟨ψ, hasWeakWordDeriv_classical Ω X hX I φ φ.contDiff.contDiffOn,
    ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport⟩

end RothschildStein.S

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakSub
public import RothschildStein.S.Sobolev
public import RothschildStein.Definitions.sobolevXENorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- The fixed Sobolev norm obeys the triangle inequality for successive
approximation errors, using uniqueness of weak word representatives. -/
theorem sobolevXENorm_sub_le_sub_add_sub {N m : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (Ω : Opens (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    {u v z : (Fin N → ℝ) → ℝ}
    (hu : memSobolevX w X Ω k p u) (hv : memSobolevX w X Ω k p v)
    (hz : memSobolevX w X Ω k p z) :
    sobolevXENorm w X Ω k p (fun x => u x-z x) ≤
      sobolevXENorm w X Ω k p (fun x => u x-v x) +
      sobolevXENorm w X Ω k p (fun x => v x-z x) := by
  classical
  unfold sobolevXENorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro I hI
  obtain ⟨a,ha,_⟩ := hu.2 I hI
  obtain ⟨b,hb,_⟩ := hv.2 I hI
  obtain ⟨c,hc,_⟩ := hz.2 I hI
  rw [S.weakWordENorm_eq X Ω I p _ _ (S.hasWeakWordDeriv_sub X Ω hX ha hc),
    S.weakWordENorm_eq X Ω I p _ _ (S.hasWeakWordDeriv_sub X Ω hX ha hb),
    S.weakWordENorm_eq X Ω I p _ _ (S.hasWeakWordDeriv_sub X Ω hX hb hc)]
  have he : (fun x => a x-c x) = (fun x => a x-b x) + (fun x => b x-c x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [he]
  exact eLpNorm_add_le hp

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakSub
public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n q : ℕ} {p : ℝ≥0∞}

/-- Differences preserve the weighted Sobolev class
(BB Def 2.2, p. 68; approximation assembly). -/
theorem memSobolevX_sub (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Opens (Fin n → ℝ))
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) (Ω : Set (Fin n → ℝ)))
    (k : ℕ) {f g : (Fin n → ℝ) → ℝ}
    (hf : memSobolevX w X Ω k p f) (hg : memSobolevX w X Ω k p g) :
    memSobolevX w X Ω k p (fun x => f x-g x) := by
  refine ⟨hf.1.sub hg.1,fun I hI => ?_⟩
  obtain ⟨a,ha,hl⟩ := hf.2 I hI
  obtain ⟨b,hb,hm⟩ := hg.2 I hI
  exact ⟨fun x => a x-b x,hasWeakWordDeriv_sub X Ω hX ha hb,hl.sub hm⟩

end RothschildStein.S

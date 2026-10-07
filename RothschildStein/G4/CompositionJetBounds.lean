-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FiniteJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- An explicit finite-order budget for composition. -/
def compositionJetBudget (h : ℕ) (C P : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (h + 1), (j.factorial : ℝ) * C * (1 + P) ^ j

/-- Quantitative composition on original open domains. The outer
budget is evaluated only at the image of the compact buffer; the inner
budget is converted to the geometric budget required by Mathlib's
Faà di Bruno estimate. -/
theorem HasJetBound.comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Ω : Set E} {D : Set F} {K : Set E} {L : Set F}
    (hΩ : IsOpen Ω) (hD : IsOpen D) (hKΩ : K ⊆ Ω)
    {f : E → F} {g : F → G}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g D)
    (hmap : MapsTo f Ω D) (hKL : MapsTo f K L)
    {h : ℕ} {P C : ℝ} (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hfP : HasJetBound Ω K f h P) (hgC : HasJetBound D L g h C) :
    HasJetBound Ω K (g ∘ f) h (compositionJetBudget h C P) := by
  intro j hj x hx
  have hb := norm_iteratedFDerivWithin_comp_le hg hf (n := j) (by simp)
    hD.uniqueDiffOn hΩ.uniqueDiffOn hmap (hKΩ hx)
    (fun i hi => hgC i (hi.trans hj) (f x) (hKL hx))
    (D := 1 + P) (fun i hi hij => (hfP i (hij.trans hj) x hx).trans
      ((by linarith : P ≤ 1 + P).trans
        (le_self_pow₀ (by linarith : 1 ≤ 1 + P) (by omega : i ≠ 0))))
  apply hb.trans
  unfold compositionJetBudget
  exact Finset.single_le_sum (f := fun i => (i.factorial : ℝ) * C * (1 + P) ^ i)
    (fun i _ => by positivity)
    (Finset.mem_range_succ_iff.mpr hj)

end RothschildStein.G4

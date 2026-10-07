-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.AdditiveJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Applying a fixed linear map multiplies finite jet budgets by
its operator norm. -/
theorem HasJetBound.linear_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Ω K : Set E} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {f : E → F} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    {h : ℕ} {P : ℝ} (hfP : HasJetBound Ω K f h P) (L : F →L[ℝ] G) :
    HasJetBound Ω K (L ∘ f) h (‖L‖ * P) := by
  intro j hj x hx
  exact (L.norm_iteratedFDerivWithin_comp_left (hf x (hKΩ hx)) hΩ.uniqueDiffOn
    (hKΩ hx) (by simp)).trans
    (mul_le_mul_of_nonneg_left (hfP j hj x hx) L.opNorm_nonneg)

/-- Evaluating a linear-map-valued coefficient at a fixed vector
uses its norm as an exact budget multiplier. -/
theorem HasJetBound.clm_apply_const {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Ω K : Set E} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {f : E → F →L[ℝ] G} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    {h : ℕ} {P : ℝ} (hfP : HasJetBound Ω K f h P) (v : F) :
    HasJetBound Ω K (fun x => f x v) h (‖v‖ * P) := by
  intro j hj x hx
  exact (norm_iteratedFDerivWithin_clm_apply_const (hf x (hKΩ hx)) hΩ.uniqueDiffOn
    (hKΩ hx) (by simp)).trans
    (mul_le_mul_of_nonneg_left (hfP j hj x hx) (norm_nonneg _))

end RothschildStein.G4

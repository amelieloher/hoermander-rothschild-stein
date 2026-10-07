-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FstParameterJetBounds
public import RothschildStein.G3.PositiveCompositionAt
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

/-- Positive endpoint bounds allow the spatial input to vary, without its value
entering the numerical composition budget. -/
theorem norm_variable_state_endpoint_jet_le {P E F G : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : P → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (H : F × E → G) (q : P × E) {n : ℕ} (hn : 1 ≤ n)
    (hH : ContDiffAt ℝ n H (f q.1,q.2))
    {C A : ℝ} (hC : 0 ≤ C) (hA : 1 ≤ A)
    (hHjet : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j H (f q.1,q.2)‖ ≤ C)
    (hfjet : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j f q.1‖ ≤ A) :
    ‖iteratedFDeriv ℝ n (fun w : P × E => H (f w.1,w.2)) q‖ ≤
      n.factorial*C*A^n := by
  let g := fun w : P × E => (f w.1,w.2)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := (hf.comp contDiff_fst).prodMk contDiff_snd
  exact norm_positive_composition_jet_at_le (f := H) (g := g) (x := q) hn hH
    (hg.contDiffAt.of_le (by simp)) hC hA hHjet
    (fun j hj hjn => norm_variable_state_parameter_jet_le f hf q hj hA (hfjet j hj hjn))
end RothschildStein.G3

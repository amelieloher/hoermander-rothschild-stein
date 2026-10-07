-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ParameterJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G1

/-- Linear reparametrization of local finite jets uses only the
operator norm of the parameter map (BB Prop 1.2, pp. 3–4). -/
theorem norm_local_linear_reparametrized_jet_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Set E} (hS : IsOpen S) {f : E → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f S) (L : G →L[ℝ] E)
    {x : G} (hx : L x ∈ S) (n : ℕ) {M D : ℝ}
    (hM : 0 ≤ M)
    (hjet : ‖iteratedFDeriv ℝ n f (L x)‖ ≤ M) (hL : ‖L‖ ≤ D) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ M * D ^ n := by
  have hpre : IsOpen (L ⁻¹' S) := hS.preimage L.continuous
  have heq := L.iteratedFDerivWithin_comp_right hf hS.uniqueDiffOn
    hpre.uniqueDiffOn hx (i := n) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hS hx,
    iteratedFDerivWithin_of_isOpen _ hpre hx] at heq
  rw [heq]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul hjet (pow_le_pow_left₀ (norm_nonneg L) hL n)
    (pow_nonneg (norm_nonneg L) n) hM

end RothschildStein.G1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.SymmetricMultilinearDiagonal

@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.G3

theorem frechet_jets_eq_of_power_error
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {n : ℕ} {C : ℝ}
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0)
    (hb : ∀ᶠ x : E in 𝓝 0, ‖f x - g x‖ ≤ C * ‖x‖ ^ (n + 1)) :
    ∀ k ≤ n, iteratedFDeriv ℝ k f 0 = iteratedFDeriv ℝ k g 0 := by
  intro k hk
  have hfk : ContDiffAt ℝ k f 0 := hf.of_le (by exact_mod_cast hk)
  have hgk : ContDiffAt ℝ k g 0 := hg.of_le (by exact_mod_cast hk)
  apply symmetric_multilinear_eq_of_diagonal
  · exact fun σ u => iteratedFDeriv_perm_of_finite_smoothness hfk σ u
  · exact fun σ u => iteratedFDeriv_perm_of_finite_smoothness hgk σ u
  · exact diagonal_frechet_jets_eq_of_power_error hf hg hb k hk

end RothschildStein.G3

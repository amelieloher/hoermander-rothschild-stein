-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FlatFrechetJets
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.G3

theorem frechet_jets_eq_of_radial_power_error
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {n : ℕ}
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0)
    (hb : ∀ v : E, ∃ C : ℝ, ∀ᶠ t : ℝ in 𝓝 0,
      ‖f (t • v) - g (t • v)‖ ≤ C * |t| ^ (n + 1)) :
    ∀ k ≤ n, iteratedFDeriv ℝ k f 0 = iteratedFDeriv ℝ k g 0 := by
  intro k hk
  apply symmetric_multilinear_eq_of_diagonal
  · exact fun σ u => iteratedFDeriv_perm_of_finite_smoothness
      (hf.of_le (by exact_mod_cast hk)) σ u
  · exact fun σ u => iteratedFDeriv_perm_of_finite_smoothness
      (hg.of_le (by exact_mod_cast hk)) σ u
  · intro v
    obtain ⟨C,hC⟩ := hb v
    let A : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v
    have hfa : ContDiffAt ℝ n (fun t : ℝ => f (t • v)) 0 := by
      have h := (show ContDiffAt ℝ n f (A 0) by simpa [A] using hf).comp 0
        A.contDiff.contDiffAt
      simpa [A, Function.comp_def] using h
    have hga : ContDiffAt ℝ n (fun t : ℝ => g (t • v)) 0 := by
      have h := (show ContDiffAt ℝ n g (A 0) by simpa [A] using hg).comp 0
        A.contDiff.contDiffAt
      simpa [A, Function.comp_def] using h
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro L
    have he := projected_curve_jets_eq_of_power_error L hfa hga hC k hk
    rw [projected_radial_deriv_eq_diagonal L v hf hk,
      projected_radial_deriv_eq_diagonal L v hg hk] at he
    exact he
end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.LocalLinearJetComposition
public import RothschildStein.G3.RadialProjectedJets
public import Mathlib.Analysis.Normed.Module.Dual

@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.G3

theorem projected_radial_deriv_eq_diagonal
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {n k : ℕ} (L : F →L[ℝ] ℝ) (v : E)
    (hf : ContDiffAt ℝ n f 0) (hk : k ≤ n) :
    iteratedDeriv k (fun t : ℝ => L (f (t • v))) 0 =
      L (iteratedFDeriv ℝ k f 0 (fun _ => v)) := by
  let A : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hfa : ContDiffAt ℝ n (f ∘ A) 0 := by
    apply (show ContDiffAt ℝ n f (A 0) by simpa [A] using hf).comp 0
    exact A.contDiff.contDiffAt
  have hleft := L.iteratedFDeriv_comp_left hfa (i := k) (by exact_mod_cast hk)
  have hright := iteratedFDeriv_comp_linear_at A 0
    (show ContDiffAt ℝ n f (A 0) by simpa [A] using hf) hk
  unfold iteratedDeriv
  change iteratedFDeriv ℝ k (L ∘ (f ∘ A)) 0 (fun _ => 1) = _
  rw [hleft, hright]
  simp [A]

theorem diagonal_frechet_jets_eq_of_power_error
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {n : ℕ} {C : ℝ}
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0)
    (hbound : ∀ᶠ x : E in 𝓝 0, ‖f x - g x‖ ≤ C * ‖x‖ ^ (n + 1)) :
    ∀ k ≤ n, ∀ v : E,
      iteratedFDeriv ℝ k f 0 (fun _ => v) =
        iteratedFDeriv ℝ k g 0 (fun _ => v) := by
  intro k hk v
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  have he := radial_projected_jets_eq_of_power_error L v hf hg hbound k hk
  rw [projected_radial_deriv_eq_diagonal L v hf hk,
    projected_radial_deriv_eq_diagonal L v hg hk] at he
  exact he

end RothschildStein.G3

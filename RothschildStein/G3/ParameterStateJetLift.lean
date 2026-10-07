-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.TaylorCompositionCongruence
public import Mathlib.Analysis.Calculus.ContDiff.Operations
@[expose] public section
noncomputable section
namespace RothschildStein.G3
variable {A P : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def parameterStateLift (x : P) (f : A × P → P) (q : A × P) : A × P :=
  (q.1,f q-x)

omit [NormedSpace ℝ A] [NormedSpace ℝ P] in
theorem parameterStateLift_zero {x : P} {f : A × P → P} (hf : f 0 = x) :
    parameterStateLift x f 0 = 0 := by simp [parameterStateLift,hf]

theorem parameterStateLift_jets_eq {n : ℕ} {x : P} {f g : A × P → P}
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0)
    (hj : ∀ k ≤ n, iteratedFDeriv ℝ k f 0 = iteratedFDeriv ℝ k g 0) :
    ∀ k ≤ n, iteratedFDeriv ℝ k (parameterStateLift x f) 0 =
      iteratedFDeriv ℝ k (parameterStateLift x g) 0 := by
  intro k hk
  have hf' : ContDiffAt ℝ k f 0 := hf.of_le (by exact_mod_cast hk)
  have hg' : ContDiffAt ℝ k g 0 := hg.of_le (by exact_mod_cast hk)
  unfold parameterStateLift
  rw [iteratedFDeriv_prodMk contDiffAt_fst (hf'.sub contDiffAt_const) le_rfl,
    iteratedFDeriv_prodMk contDiffAt_fst (hg'.sub contDiffAt_const) le_rfl]
  have he : iteratedFDeriv ℝ k (fun q => f q-x) 0 =
      iteratedFDeriv ℝ k (fun q => g q-x) 0 := by
    change iteratedFDeriv ℝ k (f-(fun _ => x)) 0 =
      iteratedFDeriv ℝ k (g-(fun _ => x)) 0
    rw [iteratedFDeriv_sub_apply hf' contDiffAt_const,
      iteratedFDeriv_sub_apply hg' contDiffAt_const, hj k hk]
  rw [he]
end RothschildStein.G3

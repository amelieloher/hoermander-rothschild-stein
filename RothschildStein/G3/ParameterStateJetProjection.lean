-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ParameterStateJetLift
@[expose] public section
noncomputable section
namespace RothschildStein.G3
variable {A P : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- State projection recovers the full point-map jets from augmented updates. -/
theorem point_jets_eq_of_parameterStateLift_jets_eq {n : ℕ} {x : P} {f g : A × P → P}
    (hf : ContDiffAt ℝ n (parameterStateLift x f) 0)
    (hg : ContDiffAt ℝ n (parameterStateLift x g) 0)
    (hfzero : f 0 = x) (hgzero : g 0 = x)
    (hj : ∀ k ≤ n, iteratedFDeriv ℝ k (parameterStateLift x f) 0 =
      iteratedFDeriv ℝ k (parameterStateLift x g) 0) :
    ∀ k ≤ n, iteratedFDeriv ℝ k f 0 = iteratedFDeriv ℝ k g 0 := by
  have he := frechet_jets_comp_eq_of_jets_eq hf hg
    (g₁ := fun z : A × P => z.2+x) (g₂ := fun z : A × P => z.2+x)
    (contDiffAt_snd.add contDiffAt_const) (contDiffAt_snd.add contDiffAt_const) hj
    (by intro k hk; rw [parameterStateLift_zero hfzero,parameterStateLift_zero hgzero])
  have hfe : (fun z : A × P => z.2+x) ∘ parameterStateLift x f = f := by
    funext q
    change f q-x+x = f q
    abel
  have hge : (fun z : A × P => z.2+x) ∘ parameterStateLift x g = g := by
    funext q
    change g q-x+x = g q
    abel
  simpa only [hfe,hge] using he
end RothschildStein.G3

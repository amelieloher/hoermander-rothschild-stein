-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.Analysis.Calculus.ContDiff.Comp
@[expose] public section
noncomputable section
namespace RothschildStein.G3
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem taylorComp_eq_of_coefficients_eq {n : ℕ}
    (q₁ q₂ : FormalMultilinearSeries ℝ F G)
    (p₁ p₂ : FormalMultilinearSeries ℝ E F)
    (hq : ∀ k ≤ n, q₁ k = q₂ k) (hp : ∀ k ≤ n, p₁ k = p₂ k) :
    q₁.taylorComp p₁ n = q₂.taylorComp p₂ n := by
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_congr rfl
  intro c _
  unfold FormalMultilinearSeries.compAlongOrderedFinpartition
  rw [hq c.length c.length_le]
  congr 1
  funext m
  exact hp (c.partSize m) (c.partSize_le m)

theorem frechet_jets_comp_eq_of_jets_eq {n : ℕ} {x : E}
    {f₁ f₂ : E → F} {g₁ g₂ : F → G}
    (hf₁ : ContDiffAt ℝ n f₁ x) (hf₂ : ContDiffAt ℝ n f₂ x)
    (hg₁ : ContDiffAt ℝ n g₁ (f₁ x))
    (hg₂ : ContDiffAt ℝ n g₂ (f₂ x))
    (hf : ∀ k ≤ n, iteratedFDeriv ℝ k f₁ x = iteratedFDeriv ℝ k f₂ x)
    (hg : ∀ k ≤ n, iteratedFDeriv ℝ k g₁ (f₁ x) =
      iteratedFDeriv ℝ k g₂ (f₂ x)) :
    ∀ k ≤ n, iteratedFDeriv ℝ k (g₁ ∘ f₁) x =
      iteratedFDeriv ℝ k (g₂ ∘ f₂) x := by
  intro k hk
  rw [iteratedFDeriv_comp hg₁ hf₁ (by exact_mod_cast hk),
    iteratedFDeriv_comp hg₂ hf₂ (by exact_mod_cast hk)]
  apply taylorComp_eq_of_coefficients_eq
  · intro j hj
    exact hg j (hj.trans hk)
  · intro j hj
    exact hf j (hj.trans hk)

theorem frechet_jets_substitution_eq {n : ℕ} {f g : F → G} {h : E → F}
    (hh : ContDiffAt ℝ n h 0) (hz : h 0 = 0)
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0)
    (hj : ∀ k ≤ n, iteratedFDeriv ℝ k f 0 = iteratedFDeriv ℝ k g 0) :
    ∀ k ≤ n, iteratedFDeriv ℝ k (f ∘ h) 0 = iteratedFDeriv ℝ k (g ∘ h) 0 := by
  apply frechet_jets_comp_eq_of_jets_eq hh hh
  · simpa only [hz] using hf
  · simpa only [hz] using hg
  · intro k hk; rfl
  · simpa only [hz] using hj
end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Piecewise

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Two C¹ time branches with matching values and full joint first derivatives on the zero-time hyperplane glue to a jointly C¹ map
(BB Thm 1.48, pp. 32–34). -/
theorem timePiecewise_contDiff_one (f g : ℝ × E → F)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hval : ∀ x, f (0, x) = g (0, x))
    (hderiv : ∀ x, fderiv ℝ f (0, x) = fderiv ℝ g (0, x)) :
    ContDiff ℝ 1 (fun q : ℝ × E => if 0 ≤ q.1 then f q else g q) := by
  classical
  let D : ℝ × E → (ℝ × E) →L[ℝ] F := fun q =>
    if 0 ≤ q.1 then fderiv ℝ f q else fderiv ℝ g q
  have hD : Continuous D := by
    apply Continuous.if _ (hf.continuous_fderiv (by norm_num)) (hg.continuous_fderiv (by norm_num))
    intro q hq
    have hh : q.1 = 0 := by
      have hmem := continuous_fst.frontier_preimage_subset (Ici (0 : ℝ)) hq
      simpa only [frontier_Ici, mem_preimage, mem_singleton_iff] using hmem
    rcases q with ⟨h, x⟩
    dsimp at hh
    subst h
    exact hderiv x
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨D, hD, ?_⟩
  intro q
  rcases q with ⟨h, x⟩
  by_cases hz : h = 0
  · subst h
    simp only [D, le_refl, ite_true]
    change HasFDerivAt (fun q : ℝ × E => if 0 ≤ q.1 then f q else g q)
      (fderiv ℝ f (0, x)) (0, x)
    rw [hasFDerivAt_iff_tendsto]
    have hp := hasFDerivAt_iff_tendsto.mp ((hf.differentiable (by norm_num) (0, x)).hasFDerivAt)
    have hm := hasFDerivAt_iff_tendsto.mp ((hg.differentiable (by norm_num) (0, x)).hasFDerivAt)
    rw [← hval x, ← hderiv x] at hm
    convert hp.if' (p := fun q : ℝ × E => 0 ≤ q.1) hm using 1
    funext q
    simp only [le_refl, ite_true]
    split_ifs <;> rfl
  · by_cases hp : 0 < h
    · have he : ∀ᶠ q : ℝ × E in 𝓝 (h, x), 0 ≤ q.1 := by
        have ht : ∀ᶠ q : ℝ × E in 𝓝 (h, x), q.1 ∈ Ioi 0 :=
          continuousAt_fst.eventually_mem (isOpen_Ioi.mem_nhds hp)
        exact ht.mono (fun q hq => hq.le)
      have hd := (hf.differentiable (by norm_num) (h, x)).hasFDerivAt
      change HasFDerivAt _ (if 0 ≤ h then fderiv ℝ f (h, x) else _) (h, x)
      rw [ite_eq_left hp.le]
      apply hd.congr_of_eventuallyEq
      filter_upwards [he] with q hq
      exact ite_eq_left hq
    · have hn : h < 0 := lt_of_le_of_ne (le_of_not_gt hp) hz
      have he : ∀ᶠ q : ℝ × E in 𝓝 (h, x), ¬0 ≤ q.1 := by
        have ht : ∀ᶠ q : ℝ × E in 𝓝 (h, x), q.1 ∈ Iio 0 :=
          continuousAt_fst.eventually_mem (isOpen_Iio.mem_nhds hn)
        exact ht.mono (fun q hq => not_le_of_gt hq)
      have hd := (hg.differentiable (by norm_num) (h, x)).hasFDerivAt
      change HasFDerivAt _ (if 0 ≤ h then _ else fderiv ℝ g (h, x)) (h, x)
      rw [ite_eq_right (not_le_of_gt hn)]
      apply hd.congr_of_eventuallyEq
      filter_upwards [he] with q hq
      exact ite_eq_right hq

end RothschildStein.G1

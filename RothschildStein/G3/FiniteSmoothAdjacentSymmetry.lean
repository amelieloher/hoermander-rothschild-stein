-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.AdjacentTupleSwaps

@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.G3

theorem iteratedFDeriv_adjacent_swap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (n : ℕ) {x : E}
    (hf : ContDiffAt ℝ (n + 1) f x) (u : Fin (n + 1) → E) (i : Fin n) :
    iteratedFDeriv ℝ (n + 1) f x
      (fun j => u (Equiv.swap i.castSucc i.succ j)) =
      iteratedFDeriv ℝ (n + 1) f x u := by
  induction n generalizing x with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, tuple_swap_leading]
      have hu : u = Fin.cons (u 0) (Fin.cons (u 1) (Fin.tail (Fin.tail u))) := by
        ext j
        refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) j <;> rfl
      rw [hu]
      simpa only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ, Fin.tail_cons] using
        iteratedFDeriv_swap_leading_pair hf (u 1) (u 0) (Fin.tail (Fin.tail u))
    · rw [tuple_swap_succ]
      have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ (n + 1) f) x :=
        hf.differentiableAt_iteratedFDeriv (by norm_cast; omega)
      rw [hD.iteratedFDeriv_succ_apply_left', hD.iteratedFDeriv_succ_apply_left']
      simp only [Fin.cons_zero, Fin.tail_cons]
      have he : (fun y => iteratedFDeriv ℝ (n + 1) f y
          (fun j => Fin.tail u (Equiv.swap i.castSucc i.succ j)))
          =ᶠ[𝓝 x] (fun y => iteratedFDeriv ℝ (n + 1) f y (Fin.tail u)) := by
        filter_upwards [hf.eventually (by simp)] with y hy
        exact ih (hy.of_le (by norm_cast; omega)) (Fin.tail u) i
      rw [he.fderiv_eq]

end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.DiagonalJets

@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.G3

theorem iteratedFDeriv_leading_pair_as_second_derivative
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {n : ℕ} {x : E}
    (hf : ContDiffAt ℝ (n + 2) f x) (v w : E) (m : Fin n → E) :
    iteratedFDeriv ℝ (n + 2) f x (Fin.cons v (Fin.cons w m)) =
      iteratedFDeriv ℝ 2 (fun y => iteratedFDeriv ℝ n f y m) x ![v, w] := by
  let G : E → F := fun y => iteratedFDeriv ℝ n f y m
  have hH : ContDiffAt ℝ 2 (iteratedFDeriv ℝ n f) x :=
    hf.iteratedFDeriv_right (by norm_cast; omega)
  have hG : ContDiffAt ℝ 2 G x :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F m).contDiff.contDiffAt.comp x hH
  have hnp1 : DifferentiableAt ℝ (iteratedFDeriv ℝ (n + 1) f) x :=
    hf.differentiableAt_iteratedFDeriv (by norm_cast; omega)
  have he : (fun y => iteratedFDeriv ℝ (n + 1) f y (Fin.cons w m))
      =ᶠ[𝓝 x] (fun y => fderiv ℝ G y w) := by
    filter_upwards [hH.eventually (by norm_num)] with y hy
    simpa only [Fin.tail_cons, Fin.cons_zero] using
      (hy.differentiableAt (by norm_num)).iteratedFDeriv_succ_apply_left'
        (f := f) (m := Fin.cons w m)
  rw [hnp1.iteratedFDeriv_succ_apply_left']
  simp only [Fin.tail_cons, Fin.cons_zero]
  rw [he.fderiv_eq]
  have hDG : DifferentiableAt ℝ (fderiv ℝ G) x :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
  change fderiv ℝ (fun y => fderiv ℝ G y w) x v =
    fderiv ℝ (fderiv ℝ G) x v w
  rw [fderiv_clm_apply hDG (differentiableAt_const w)]
  simp

theorem iteratedFDeriv_swap_leading_pair
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {n : ℕ} {x : E}
    (hf : ContDiffAt ℝ (n + 2) f x) (v w : E) (m : Fin n → E) :
    iteratedFDeriv ℝ (n + 2) f x (Fin.cons v (Fin.cons w m)) =
      iteratedFDeriv ℝ (n + 2) f x (Fin.cons w (Fin.cons v m)) := by
  have hH : ContDiffAt ℝ 2 (iteratedFDeriv ℝ n f) x :=
    hf.iteratedFDeriv_right (by norm_cast; omega)
  have hG : ContDiffAt ℝ 2 (fun y => iteratedFDeriv ℝ n f y m) x :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F m).contDiff.contDiffAt.comp x hH
  rw [iteratedFDeriv_leading_pair_as_second_derivative hf v w m,
    iteratedFDeriv_leading_pair_as_second_derivative hf w v m]
  exact (hG.isSymmSndFDerivAt (by norm_num)).iteratedFDeriv_cons

end RothschildStein.G3

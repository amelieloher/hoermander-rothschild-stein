-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.ZeroBoundaryFirstMoment
import Mathlib.Tactic

/-! # Continuity of first moments in the zero-boundary graph norm -/

@[expose] public section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology
namespace HeatKernel.Sobolev

/-- First-moment norms converge under graph convergence on a finite-volume domain. -/
theorem tendsto_firstMoment_of_zeroBoundaryGraph {N q : ℕ} {ι : Type*}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hfinite : volume (U : Set (Fin N → ℝ)) ≠ ⊤)
    {l : Filter ι} {v : ι → zeroBoundaryGraph U X} {w : zeroBoundaryGraph U X}
    (hconv : Tendsto v l (𝓝 w)) :
    Tendsto (fun n => (eLpNorm (v n : GradientSpace (N := N) ⊤ q).fst 1 volume).toReal)
      l (𝓝 (eLpNorm (w : GradientSpace (N := N) ⊤ q).fst 1 volume).toReal) := by
  let hv := fun n => (memLp_one_zeroBoundaryGraph U X hfinite (v n)).1
  let hw := (memLp_one_zeroBoundaryGraph U X hfinite w).1
  let a : ι → Lp ℝ 1 volume := fun n => (hv n).toLp (v n : GradientSpace (N := N) ⊤ q).fst
  let b : Lp ℝ 1 volume := hw.toLp (w : GradientSpace (N := N) ⊤ q).fst
  have he (n : ι) :
      ‖a n - b‖ = (eLpNorm
        ((v n - w : zeroBoundaryGraph U X) : GradientSpace (N := N) ⊤ q).fst 1 volume).toReal := by
    rw [Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    have hsub := (Lp.coeFn_sub (a n) b).trans ((hv n).coeFn_toLp.sub hw.coeFn_toLp)
    have htarget := Lp.coeFn_sub (v n : GradientSpace (N := N) ⊤ q).fst
      (w : GradientSpace (N := N) ⊤ q).fst
    simp only [Opens.coe_top, Measure.restrict_univ] at htarget
    simpa only [Submodule.coe_sub, WithLp.sub_fst] using hsub.trans htarget.symm
  have ht : Tendsto a l (𝓝 b) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [dist_eq_norm, he] using
      tendsto_firstMoment_difference_zero_of_zeroBoundaryGraph U X hfinite hconv
  have hnorm := ht.norm
  simpa only [a, b, Lp.norm_toLp] using hnorm

end HeatKernel.Sobolev

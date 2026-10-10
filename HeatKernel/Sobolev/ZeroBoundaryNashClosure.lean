-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.ZeroBoundaryFirstMomentContinuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-! # Extending Nash inequalities from the smooth core -/

@[expose] public section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology
namespace HeatKernel.Sobolev

/-- A Nash-type norm bound on the interior smooth core passes to its graph closure. -/
theorem norm_sq_le_nash_on_zeroBoundaryGraph_of_core {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hfinite : volume (U : Set (Fin N → ℝ)) ≠ ⊤)
    {C A B a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcore : ∀ w : zeroBoundaryGraph U X,
      (w : GradientSpace (N := N) ⊤ q) ∈ interiorGradientPairs U X →
      ‖(w : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤
        C * (A * ‖(w : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
          B * ‖(w : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ^ a *
          (eLpNorm (w : GradientSpace (N := N) ⊤ q).fst 1 volume).toReal ^ b)
    (v : zeroBoundaryGraph U X) :
    ‖(v : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤
      C * (A * ‖(v : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        B * ‖(v : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ^ a *
        (eLpNorm (v : GradientSpace (N := N) ⊤ q).fst 1 volume).toReal ^ b := by
  obtain ⟨w, hw, ht⟩ := exists_interiorGradientPairs_tendsto U X v
  let z : ℕ → zeroBoundaryGraph U X := fun n =>
    ⟨w n, interiorGradientPairs_subset_zeroBoundaryGraph U X (hw n)⟩
  have hz : Tendsto z atTop (𝓝 v) := tendsto_subtype_rng.mpr ht
  have hf := ((tendsto_GradientSpace_iff ⊤).mp ht).1
  have hg : Tendsto (fun n => (w n).snd) atTop
      (𝓝 (v : GradientSpace (N := N) ⊤ q).snd) := by
    exact continuous_snd.continuousAt.tendsto.comp
      ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous.continuousAt.tendsto.comp ht)
  have he := ((tendsto_const_nhds (x := A)).mul (hg.norm.pow 2)).add
    ((tendsto_const_nhds (x := B)).mul (hf.norm.pow 2))
  have hm := tendsto_firstMoment_of_zeroBoundaryGraph U X hfinite hz
  have hr := ((tendsto_const_nhds (x := C)).mul (he.rpow_const (Or.inr ha))).mul
    (hm.rpow_const (Or.inr hb))
  exact le_of_tendsto_of_tendsto (hf.norm.pow 2) hr
    (Eventually.of_forall fun n => hcore (z n) (hw n))

end HeatKernel.Sobolev

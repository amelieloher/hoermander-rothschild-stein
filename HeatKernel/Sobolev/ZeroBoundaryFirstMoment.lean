-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.FiniteSupportFirstMoment
public import HeatKernel.Sobolev.ZeroBoundarySupport
import Mathlib.Tactic

/-! # First moments on zero-boundary form domains -/

@[expose] public section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology
namespace HeatKernel.Sobolev

/-- Support almost everywhere is sufficient for the finite-volume L²-to-L¹ estimate. -/
theorem memLp_one_and_toReal_le_of_ae_eq_zero_outside
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} {B : Set α} (hB : MeasurableSet B)
    (hf : MemLp f 2 μ) (hzero : ∀ᵐ x ∂μ, x ∉ B → f x = 0) (hfinite : μ B ≠ ⊤) :
    MemLp f 1 μ ∧ (eLpNorm f 1 μ).toReal ≤
      (eLpNorm f 2 μ).toReal * (μ B).toReal ^ (1 / 2 : ℝ) := by
  have heq : B.indicator f =ᵐ[μ] f := by
    filter_upwards [hzero] with x hx
    by_cases hmem : x ∈ B
    · simp only [indicator_of_mem hmem]
    · simp only [indicator_of_notMem hmem, hx hmem]
  have hsupport : Function.support (B.indicator f) ⊆ B := by
    intro x hx
    by_contra hnot
    exact hx (indicator_of_notMem hnot f)
  have hind : MemLp (B.indicator f) 2 μ := hf.indicator hB
  have H : MemLp (B.indicator f) 1 μ ∧
      (eLpNorm (B.indicator f) 1 μ).toReal ≤
        (eLpNorm (B.indicator f) 2 μ).toReal * (μ B).toReal ^ (1 / 2 : ℝ) :=
    memLp_one_and_toReal_le_of_support_subset hind hsupport hfinite
  have he₁ := eLpNorm_congr_ae (p := 1) heq
  have he₂ := eLpNorm_congr_ae (p := 2) heq
  constructor
  · change eLpNorm f 1 μ < ⊤
    rw [← he₁]
    exact H.1
  · rw [← he₁, ← he₂]
    exact H.2

/-- Zero-boundary graph functions on a finite-volume domain have a controlled first moment. -/
theorem memLp_one_zeroBoundaryGraph {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hfinite : volume (U : Set (Fin N → ℝ)) ≠ ⊤) (v : zeroBoundaryGraph U X) :
    MemLp (v : GradientSpace (N := N) ⊤ q).fst 1 volume ∧
      (eLpNorm (v : GradientSpace (N := N) ⊤ q).fst 1 volume).toReal ≤
        ‖(v : GradientSpace (N := N) ⊤ q).fst‖ *
          (volume (U : Set (Fin N → ℝ))).toReal ^ (1 / 2 : ℝ) := by
  have hf : MemLp (v : GradientSpace (N := N) ⊤ q).fst 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      (Lp.memLp (v : GradientSpace (N := N) ⊤ q).fst)
  have H := memLp_one_and_toReal_le_of_ae_eq_zero_outside U.isOpen.measurableSet hf
    (ae_eq_zero_outside_of_mem_zeroBoundaryGraph U X v) hfinite
  simpa only [Lp.norm_def, Opens.coe_top, Measure.restrict_univ] using H

/-- Graph convergence on a fixed finite-volume domain implies convergence of first-moment differences. -/
theorem tendsto_firstMoment_difference_zero_of_zeroBoundaryGraph
    {N q : ℕ} {ι : Type*} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hfinite : volume (U : Set (Fin N → ℝ)) ≠ ⊤)
    {l : Filter ι} {v : ι → zeroBoundaryGraph U X} {w : zeroBoundaryGraph U X}
    (hconv : Tendsto v l (𝓝 w)) :
    Tendsto (fun n => (eLpNorm
      ((v n - w : zeroBoundaryGraph U X) : GradientSpace (N := N) ⊤ q).fst 1 volume).toReal)
      l (𝓝 0) := by
  have hf := ((tendsto_GradientSpace_iff ⊤).mp
    (continuous_subtype_val.continuousAt.tendsto.comp hconv)).1
  have hn : Tendsto (fun n =>
      ‖((v n - w : zeroBoundaryGraph U X) : GradientSpace (N := N) ⊤ q).fst‖) l (𝓝 0) := by
    simpa only [Submodule.coe_sub, WithLp.sub_fst, Function.comp_def, sub_self, norm_zero] using
      (hf.sub (tendsto_const_nhds (x := (w : GradientSpace (N := N) ⊤ q).fst))).norm
  apply squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
    (Eventually.of_forall fun n => (memLp_one_zeroBoundaryGraph U X hfinite (v n - w)).2)
  simpa only [zero_mul] using hn.mul_const
    ((volume (U : Set (Fin N → ℝ))).toReal ^ (1 / 2 : ℝ))

end HeatKernel.Sobolev

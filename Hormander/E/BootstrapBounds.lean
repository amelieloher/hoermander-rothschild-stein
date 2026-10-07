-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.SobolevScale
public import Hormander.B.Extension.Localized
public import Hormander.B.Extension.Continuity
public import Hormander.B.Multipliers
public import Hormander.B.Mollifier.EFacing
public import Hormander.B.Nested.RealDiffOps

@[expose] public section

noncomputable section

open SchwartzMap TemperedDistribution
open Hormander.B

namespace Hormander.E

/-- A real Schwartz multiplier acts boundedly on every bundled Sobolev
space, with its Section B order constant. -/
theorem realCutoff_sobolev_bound {N : ℕ} (η : SchwartzMap (Carrier N) ℝ) (r : ℝ) :
    ∃ C : NNReal, ∀ u : Hormander.A.SobolevSpace N r,
      ∃ v : Hormander.A.SobolevSpace N r,
        v.toDistr = cutoffDistr η u.toDistr ∧ ‖v‖ ≤ (C : ℝ) * ‖u‖ := by
  let T : Operator N := realMultiplierOperator η
  have hT : HasBilinearTranspose T T := by
    exact extMultiplier_transpose η
  have hcT : Continuous (fun φ : TestFunction N => T φ) := by
    exact (realMultiplierOperator_hasContinuousTranspose η).transpose_continuous hT
  have horder : HasOrder 0 T := by
    change HasOrder 0 (multiplierOperator (complexifyRealSchwartz η))
    exact (peetre_and_multiplier_order (N := N)).2 _
  obtain ⟨_, _, hglobal⟩ := global_extension hT hcT horder
  obtain ⟨C, _, hmap⟩ := hglobal r
  refine ⟨C, fun u => ?_⟩
  obtain ⟨hu, hdist, hunorm⟩ := Hormander.A.sobolev_mono_norm
    (s₁ := r + 0) (s₂ := r) (by simp) u
  obtain ⟨v, hv, hvnorm⟩ := hmap hu
  have heq : tempExtension T hcT hu.toDistr = cutoffDistr η u.toDistr := by
    rw [hdist]
    ext φ
    rfl
  refine ⟨v, ?_, ?_⟩
  · rw [heq] at hv
    exact hv
  · exact le_trans hvnorm
      (mul_le_mul_of_nonneg_left hunorm (NNReal.coe_nonneg C))

/-- A localized input cutoff followed by its outer cutoff is the same
tempered distribution as the inner localization. -/
theorem cutoffDistr_nested_eq {N : ℕ}
    {η η' : Carrier N → ℝ} (h : Hormander.D.cutoffPrecedes η η')
    (u : Tempered N) :
    cutoffDistr (Hormander.B.cutoffSchwartz h)
        (cutoffDistr (Hormander.B.cutoffSchwartzOuter h) u) =
      cutoffDistr (Hormander.B.cutoffSchwartz h) u := by
  have hM : ∀ φ : TestFunction N,
      realMultiplierOperator (Hormander.B.cutoffSchwartzOuter h)
          (realMultiplierOperator (Hormander.B.cutoffSchwartz h) φ) =
        realMultiplierOperator (Hormander.B.cutoffSchwartz h) φ := by
    intro φ
    ext x
    rw [realMultiplierOperator_apply, realMultiplierOperator_apply,
      Hormander.B.cutoffSchwartz_apply]
    by_cases hη : η x = 0
    · simp [hη]
    · have hx : x ∈ tsupport (Hormander.B.cutoffSchwartz h : Carrier N → ℝ) := by
        apply subset_tsupport
        apply Function.mem_support.mpr
        simpa [Hormander.B.cutoffSchwartz_apply] using hη
      have houter : Hormander.B.cutoffSchwartzOuter h x = 1 :=
        Hormander.B.cutoff_outer_eq_one h x hx
      rw [houter]
      simp
  ext φ
  change u (realMultiplierOperator (Hormander.B.cutoffSchwartzOuter h)
      (realMultiplierOperator (Hormander.B.cutoffSchwartz h) φ)) =
    u (realMultiplierOperator (Hormander.B.cutoffSchwartz h) φ)
  exact congrArg (fun ψ : TestFunction N => u ψ) (hM φ)

/-- Real Schwartz cutoffs which agree pointwise induce the same
localization on tempered distributions. -/
theorem cutoffDistr_congr {N : ℕ} {η η' : SchwartzMap (Carrier N) ℝ}
    (hη : ∀ x, η x = η' x) (u : Tempered N) :
    cutoffDistr η u = cutoffDistr η' u := by
  have hM : realMultiplierOperator η = realMultiplierOperator η' := by
    apply LinearMap.ext
    intro φ
    ext x
    rw [realMultiplierOperator_apply, realMultiplierOperator_apply, hη x]
  ext φ
  change u (realMultiplierOperator η φ) = u (realMultiplierOperator η' φ)
  exact congrArg (fun ψ : TestFunction N => u ψ) (congrArg (fun T : Operator N => T φ) hM)

/-- The canonical cutoff multiplier is the distributional multiplier by
its underlying real function. -/
theorem cutoffDistr_eq_raw_function {N : ℕ} (η : SchwartzMap (Carrier N) ℝ)
    (ψ : Carrier N → ℝ) (hη : ∀ x, η x = ψ x) (u : Tempered N) :
    cutoffDistr η u =
      TemperedDistribution.smulLeftCLM ℂ (fun x => ((ψ x : ℝ) : ℂ)) u := by
  ext φ
  rw [cutoffDistr_apply_apply, TemperedDistribution.smulLeftCLM_apply_apply]
  congr 1
  have hfun : (fun x => ((η x : ℝ) : ℂ)) =
      (fun x => ((ψ x : ℝ) : ℂ)) := by
    funext x
    exact congrArg Complex.ofReal (hη x)
  have hgrowth : (fun x => ((ψ x : ℝ) : ℂ)).HasTemperateGrowth := by
    rw [← hfun]
    exact (Hormander.B.complexifyRealSchwartz η).hasTemperateGrowth
  ext x
  rw [realMultiplierOperator_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply hgrowth]
  rw [hη x]
  rfl

end Hormander.E

end

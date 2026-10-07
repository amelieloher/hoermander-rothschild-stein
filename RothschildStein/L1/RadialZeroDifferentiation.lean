-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RadialFrameDifferentiation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology BigOperators
namespace RothschildStein.L1

/-- Differentiating a zero radial sum keeps all field derivatives. -/
theorem radial_zero_differential_identity {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (R : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hR : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (R i) Ω)
    (hrad : ∀ u ∈ Ω, ∑ i, u i • R i u = 0)
    {u : Fin N → ℝ} (hu : u ∈ Ω) (j : Fin N) :
    (0 : Fin N → ℝ) = R j u + ∑ i, u i •
      VectorField.lieBracket ℝ (fun _ => Pi.single j 1) (R i) u := by
  let A := fun i => (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)
  have hdR (i : Fin N) := ((hR i).contDiffAt (Ω.isOpen.mem_nhds hu)).differentiableAt (by simp)
  have hi (i : Fin N) : HasFDerivAt (fun v => v i • R i v)
      (u i • fderiv ℝ (R i) u + (A i).smulRight (R i u)) u :=
    (A i).hasFDerivAt.fun_smul (hdR i).hasFDerivAt
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
  have he : (fun v : Fin N → ℝ => ∑ i, v i • R i v) =ᶠ[𝓝 u] (fun _ => 0) :=
    Filter.Eventually.mono (Ω.isOpen.mem_nhds hu) (fun v hv => hrad v hv)
  have hc := hs.congr_of_eventuallyEq he.symm
  have hl := congrArg (fun B => B (Pi.single j 1)) (hc.unique (hasFDerivAt_const (0 : Fin N → ℝ) u))
  simp only [sum_apply,add_apply,ContinuousLinearMap.smulRight_apply,
    smul_apply,zero_apply,Finset.sum_add_distrib,A,ContinuousLinearMap.proj_apply] at hl
  simp only [VectorField.lieBracket,fderiv_const_apply,zero_apply,sub_zero]
  simpa [Pi.single_apply,add_comm] using hl.symm
end RothschildStein.L1

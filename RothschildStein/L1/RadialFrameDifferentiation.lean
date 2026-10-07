-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FreeCanonicalCharts
public import RothschildStein.L1.CanonicalChartIdentities
public import RothschildStein.L1.CanonicalBracketAssembly
public import RothschildStein.L1.CanonicalSmoothLocalCharts
public import RothschildStein.L1.CanonicalChartSmallPatch
public import RothschildStein.L1.CanonicalExponential
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology BigOperators
namespace RothschildStein.L1

/-- Differentiate a radial decomposition in a real normed vector space. -/
theorem radial_differential_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (Ω : Opens E) (A : Fin n → E →L[ℝ] ℝ) (Z : Fin n → E → E)
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    (hrad : ∀ u ∈ Ω, ∑ i, A i u • Z i u = u)
    {u : E} (hu : u ∈ Ω) (d : E) :
    d = (∑ i, A i d • Z i u) + ∑ i, A i u • VectorField.lieBracket ℝ (fun _ => d) (Z i) u := by
  have hdZ (i : Fin n) := ((hZ i).contDiffAt (Ω.isOpen.mem_nhds hu)).differentiableAt (by simp)
  have hi (i : Fin n) : HasFDerivAt (fun v => A i v • Z i v)
      (A i u • fderiv ℝ (Z i) u + (A i).smulRight (Z i u)) u :=
    (A i).hasFDerivAt.fun_smul (hdZ i).hasFDerivAt
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
  have he : (fun v : E => ∑ i, A i v • Z i v) =ᶠ[𝓝 u] id :=
    Filter.Eventually.mono (Ω.isOpen.mem_nhds hu) (fun v hv => hrad v hv)
  have hid := hs.congr_of_eventuallyEq he.symm
  have hl := congrArg (fun B => B d) (hid.unique (hasFDerivAt_id u))
  simp only [sum_apply, add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, ContinuousLinearMap.id_apply, Finset.sum_add_distrib] at hl
  simp only [VectorField.lieBracket, fderiv_const_apply, zero_apply, sub_zero]
  simpa only [add_comm] using hl.symm

/-- Differentiating the actual radial identity produces BB
(10.17), retaining the actual coefficient derivatives. -/
theorem radial_frame_coordinate_identity {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (Z : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    (hrad : ∀ u ∈ Ω, ∑ i, u i • Z i u = u)
    {u : Fin N → ℝ} (hu : u ∈ Ω) (j : Fin N) :
    Pi.single j (1 : ℝ) = Z j u + ∑ i, u i •
      VectorField.lieBracket ℝ (fun _ => Pi.single j 1) (Z i) u := by
  have h := radial_differential_identity Ω
    (fun i => (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)) Z hZ hrad hu (Pi.single j 1)
  simpa [Pi.single_apply] using h
end RothschildStein.L1

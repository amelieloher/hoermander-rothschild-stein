-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionSpatialWeights
public import HeatKernel.Moser.TimeAverageFunctionals
public import HeatKernel.Moser.BoundedNonlinearEnergyEndpoints

import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic

/-! # Spatially weighted nonlinear energies and their time chain rule -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped NNReal
namespace HeatKernel

/-- The spatially weighted normalized primitive energy. -/
def WeakSolutionSpatialWeight.energy {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} (W : WeakSolutionSpatialWeight V X)
    (T : WeakSolutionScalarTest) (z : zeroBoundaryGraph V X) : ℝ :=
  ∫ x, W.toFun x * T.primitive ((z : GradientSpace (N := N) ⊤ q).fst x)

/-- The first variation is the value pairing with the spatially weighted nonlinear test. -/
theorem WeakSolutionSpatialWeight.exists_hasFDerivAt_energy {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (T : WeakSolutionScalarTest) (z : zeroBoundaryGraph V X) :
    ∃ D : zeroBoundaryGraph V X →L[ℝ] ℝ,
      HasFDerivAt (W.energy T) D z ∧
      ∀ k, D k = zeroBoundaryValueFunctional V X k (W.energyMap hX T z) := by
  let P : zeroBoundaryGraph V X →L[ℝ] SpatialL2 (N := N) ⊤ :=
    (energyInclusion ⊤ X).comp (zeroBoundaryEnergyInclusion V X)
  have hP (w : zeroBoundaryGraph V X) : P w = (w : GradientSpace (N := N) ⊤ q).fst := rfl
  have hd : deriv T.primitive = T.toFun := funext fun s => (T.hasDerivAt_primitive s).deriv
  have hdiff : Differentiable ℝ T.primitive := fun s =>
    (T.hasDerivAt_primitive s).differentiableAt
  have hLip : LipschitzWith T.bound (deriv T.primitive) := hd.symm ▸ T.lipschitz
  have hdz : deriv T.primitive 0 = 0 := by rw [hd, T.map_zero]
  have hm : AEStronglyMeasurable W.toFun
      (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using W.aestronglyMeasurable
  have hb : ∀ᵐ x ∂volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)),
      ‖W.toFun x‖ ≤ W.bound := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using W.norm_le
  obtain ⟨f, hf, hfD⟩ := exists_hasFDerivAt_weighted_nonlinear_energy
    hdiff hLip T.primitive_zero hdz hm W.bound.coe_nonneg hb (P z)
  refine ⟨(innerSL ℝ f).comp P, ?_, ?_⟩
  · change HasFDerivAt (fun w : zeroBoundaryGraph V X =>
      ∫ x, W.toFun x * T.primitive ((w : GradientSpace (N := N) ⊤ q).fst x)) _ z
    simpa only [Function.comp_def, hP, Opens.coe_top, Measure.restrict_univ]
      using hfD.comp z P.hasFDerivAt
  · intro k
    have hf' : f =ᵐ[volume] fun x =>
        W.toFun x * T.toFun ((z : GradientSpace (N := N) ⊤ q).fst x) := by
      simpa only [hP, hd, Opens.coe_top, Measure.restrict_univ] using hf
    change inner ℝ f (P k) = zeroBoundaryValueFunctional V X k (W.energyMap hX T z)
    rw [L2.inner_def, zeroBoundaryValueFunctional_apply]
    simp only [Opens.coe_top, Measure.restrict_univ]
    apply integral_congr_ae
    filter_upwards [hf', W.energyMap_value_ae hX T z] with x hx hy
    simp only [Real.inner_apply, hx, hy, hP]
    exact mul_comm _ _

/-- The spatially weighted energy is continuous in the zero-boundary graph norm. -/
theorem WeakSolutionSpatialWeight.continuous_energy {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (T : WeakSolutionScalarTest) : Continuous (W.energy T) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨_, hd, _⟩ := W.exists_hasFDerivAt_energy hX T z
  exact hd.continuousAt

/-- The energy along time averages is absolutely continuous using only the scalar
value bound of the original energy curve. -/
theorem WeakSolutionSpatialWeight.absolutelyContinuousOnInterval_energy_average {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (T : WeakSolutionScalarTest)
    {v : ℝ → zeroBoundaryGraph V X} (hv : MemLp v 2 volume) {M : ℝ≥0}
    (hb : ∀ᵐ t ∂volume, ‖(v t : GradientSpace (N := N) ⊤ q).fst‖ ≤ M)
    {h : ℝ} (hh : 0 < h) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => W.energy T (forwardTimeAverage h v t)) a b := by
  let P : zeroBoundaryGraph V X →L[ℝ] SpatialL2 (N := N) ⊤ :=
    (energyInclusion ⊤ X).comp (zeroBoundaryEnergyInclusion V X)
  have hP (w : zeroBoundaryGraph V X) : P w = (w : GradientSpace (N := N) ⊤ q).fst := rfl
  have hd : deriv T.primitive = T.toFun := funext fun s => (T.hasDerivAt_primitive s).deriv
  have hdiff : Differentiable ℝ T.primitive := fun s =>
    (T.hasDerivAt_primitive s).differentiableAt
  have hLip : LipschitzWith T.bound (deriv T.primitive) := hd.symm ▸ T.lipschitz
  have hdz : deriv T.primitive 0 = 0 := by rw [hd, T.map_zero]
  have hm : AEStronglyMeasurable W.toFun
      (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using W.aestronglyMeasurable
  have hwb : ∀ᵐ x ∂volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)),
      ‖W.toFun x‖ ≤ W.bound := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using W.norm_le
  have hAC := absolutelyContinuousOnInterval_nonlinear_energy_forwardTimeAverage
    hdiff hLip T.primitive_zero hdz hm hwb
    ((P.comp_memLp' hv).locallyIntegrable (by norm_num)) hb hh a b
  have he : (fun t => ∫ x, W.toFun x * T.primitive (forwardTimeAverage h (P ∘ v) t x)
      ∂volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))) =
      fun t => W.energy T (forwardTimeAverage h v t) := by
    funext t
    rw [← map_forwardTimeAverage_of_locallyIntegrable P (hv.locallyIntegrable (by norm_num)) h t]
    simp only [hP, Opens.coe_top, Measure.restrict_univ, WeakSolutionSpatialWeight.energy]
  rwa [he] at hAC

/-- The spatially weighted nonlinear chain rule along forward energy averages. -/
theorem WeakSolutionSpatialWeight.ae_hasDerivAt_energy_forwardTimeAverage {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (T : WeakSolutionScalarTest) {v : ℝ → zeroBoundaryGraph V X}
    (hv : LocallyIntegrable v volume) (h : ℝ) :
    ∀ᵐ t ∂volume, HasDerivAt (fun s => W.energy T (forwardTimeAverage h v s))
      (zeroBoundaryValueFunctional V X (h⁻¹ • (v (t + h) - v t))
        (W.energyMap hX T (forwardTimeAverage h v t))) t := by
  filter_upwards [ae_hasDerivAt_forwardTimeAverage hv h] with t ht
  obtain ⟨D, hD, haction⟩ := W.exists_hasFDerivAt_energy hX T (forwardTimeAverage h v t)
  simpa only [Function.comp_def, haction] using hD.comp_hasDerivAt t ht

end HeatKernel

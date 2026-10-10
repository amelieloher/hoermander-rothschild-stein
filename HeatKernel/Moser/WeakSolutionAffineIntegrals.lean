-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionAffineEnergyIdentity

/-! # Integral representatives of affine-corrected nonlinear energies -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

variable {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}

/-- The bounded spatial weight times a normalized primitive is integrable. -/
theorem WeakSolutionSpatialWeight.integrable_energy_density (W : WeakSolutionSpatialWeight V X)
    (T : WeakSolutionScalarTest) (z : zeroBoundaryGraph V X) :
    Integrable (fun x => W.toFun x * T.primitive ((z : GradientSpace (N := N) ⊤ q).fst x))
      volume := by
  have hd : deriv T.primitive = T.toFun := funext fun s => (T.hasDerivAt_primitive s).deriv
  have hdiff : Differentiable ℝ T.primitive := fun s =>
    (T.hasDerivAt_primitive s).differentiableAt
  have hLip : LipschitzWith T.bound (deriv T.primitive) := hd.symm ▸ T.lipschitz
  have hz := integrable_weighted_nonlinearity_of_lipschitz_deriv hdiff hLip
    T.primitive_zero (by rw [hd, T.map_zero])
    (by simpa only [Opens.coe_top, Measure.restrict_univ] using W.aestronglyMeasurable)
    W.bound.coe_nonneg
    (by simpa only [Opens.coe_top, Measure.restrict_univ] using W.norm_le)
    (z : GradientSpace (N := N) ⊤ q).fst
  simpa only [Opens.coe_top, Measure.restrict_univ] using hz

/-- Realizing the spatial weight as a fixed form test makes its value pairing
the literal weighted linear primitive. -/
theorem WeakSolutionSpatialWeight.valueFunctional_eq_integral (W : WeakSolutionSpatialWeight V X)
    (w : zeroBoundaryGraph V X)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (z : zeroBoundaryGraph V X) :
    zeroBoundaryValueFunctional V X z w =
      ∫ x, W.toFun x * (z : GradientSpace (N := N) ⊤ q).fst x := by
  rw [zeroBoundaryValueFunctional_apply]
  apply integral_congr_ae
  filter_upwards [hw] with x hx
  rw [hx, mul_comm]

/-- The affine-corrected graph energy is the integral of the affine-corrected
scalar primitive, without an additional integrability hypothesis. -/
theorem WeakSolutionSpatialWeight.affineEnergy_eq_integral (W : WeakSolutionSpatialWeight V X)
    (T : WeakSolutionScalarTest) (w : zeroBoundaryGraph V X) (c : ℝ)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (z : zeroBoundaryGraph V X) :
    W.affineEnergy T w c z = ∫ x, W.toFun x *
      (T.primitive ((z : GradientSpace (N := N) ⊤ q).fst x) +
        c * (z : GradientSpace (N := N) ⊤ q).fst x) := by
  have hz : MemLp (z : GradientSpace (N := N) ⊤ q).fst 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp (z : GradientSpace (N := N) ⊤ q).fst
  have hwLp : MemLp W.toFun 2 volume := by
    have hm : MemLp (w : GradientSpace (N := N) ⊤ q).fst 2 volume := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        Lp.memLp (w : GradientSpace (N := N) ⊤ q).fst
    exact (memLp_congr_ae hw).mp hm
  have hl : Integrable (fun x => W.toFun x *
      (z : GradientSpace (N := N) ⊤ q).fst x) volume := hwLp.integrable_mul hz
  unfold WeakSolutionSpatialWeight.affineEnergy WeakSolutionSpatialWeight.energy
  rw [W.valueFunctional_eq_integral w hw z, ← integral_const_mul,
    ← integral_add (W.integrable_energy_density T z) (hl.const_mul c)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

/-- A localization plateau identifies the corrected primitive with its original
local-solution representative. -/
theorem WeakSolutionSpatialWeight.affineEnergy_eq_integral_of_plateau
    (W : WeakSolutionSpatialWeight V X) (T : WeakSolutionScalarTest)
    (w : zeroBoundaryGraph V X) (c : ℝ)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    {u φ : (Fin N → ℝ) → ℝ} (z : zeroBoundaryGraph V X)
    (hval : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] fun x => u x * φ x)
    (hplateau : ∀ x, W.toFun x ≠ 0 → φ x = 1) :
    W.affineEnergy T w c z = ∫ x, W.toFun x * (T.primitive (u x) + c * u x) := by
  rw [W.affineEnergy_eq_integral T w c hw z]
  apply integral_congr_ae
  filter_upwards [hval] with x hx
  by_cases hW : W.toFun x = 0
  · simp only [hW, zero_mul]
  · rw [hx, hplateau x hW, mul_one]

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionLinearEnergyIdentity
public import HeatKernel.Moser.WeakSolutionSpatialTransport
public import HeatKernel.Moser.WeakSolutionEnergyInterface
public import HeatKernel.Moser.WeakSolutionSpatialEnergyIdentity
public import HeatKernel.Moser.WeakSolutionAffineTesting

import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.NormedSpace
import all Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # Affine corrections in spatially weighted nonlinear testing

A fixed spatial test restores the constant part of the scalar derivative. Its
linear value pairing restores the corresponding linear primitive term. Thus the
centering of logarithmic and power tests can be undone without changing their
principal chain-rule energy.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped NNReal
namespace HeatKernel

variable {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}

/-- The weighted nonlinear energy with its linear primitive correction. -/
def WeakSolutionSpatialWeight.affineEnergy (W : WeakSolutionSpatialWeight V X)
    (T : WeakSolutionScalarTest) (w : zeroBoundaryGraph V X) (c : ℝ)
    (z : zeroBoundaryGraph V X) : ℝ :=
  W.energy T z + c * zeroBoundaryValueFunctional V X z w

/-- The spatially weighted test with the constant derivative correction restored. -/
def WeakSolutionSpatialWeight.affineEnergyMap (W : WeakSolutionSpatialWeight V X)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (T : WeakSolutionScalarTest)
    (w : zeroBoundaryGraph V X) (c : ℝ) (z : zeroBoundaryGraph V X) : zeroBoundaryGraph V X :=
  W.energyMap hX T z + c • w

/-- A fixed test representing the spatial weight restores the uncentered scalar test. -/
theorem WeakSolutionSpatialWeight.affineEnergyMap_value_ae (W : WeakSolutionSpatialWeight V X)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (T : WeakSolutionScalarTest)
    (w : zeroBoundaryGraph V X) (c : ℝ)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (z : zeroBoundaryGraph V X) :
    (W.affineEnergyMap hX T w c z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => W.toFun x * (T.toFun ((z : GradientSpace (N := N) ⊤ q).fst x) + c) := by
  change ((W.energyMap hX T z : GradientSpace (N := N) ⊤ q).fst +
    c • (w : GradientSpace (N := N) ⊤ q).fst) =ᵐ[volume] _
  have hadd := Lp.coeFn_add (W.energyMap hX T z : GradientSpace (N := N) ⊤ q).fst
    (c • (w : GradientSpace (N := N) ⊤ q).fst)
  have hsmul := Lp.coeFn_smul c (w : GradientSpace (N := N) ⊤ q).fst
  simp only [Opens.coe_top, Measure.restrict_univ] at hadd hsmul
  filter_upwards [hadd, hsmul, W.energyMap_value_ae hX T z, hw] with x hx hc hy hz
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hc
  rw [hx, hc, hy, hz]
  ring

/-- At almost every pair of endpoints, the affine-corrected energy is paired with
the affine-corrected test. All local time assumptions come from the weak cutoff pair. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.ae_affine_spatial_energy_endpoint_identity
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B : ℝ}
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F) :
    ∀ᵐ a ∂volume, ∀ᵐ b ∂volume, ∀ W : WeakSolutionSpatialWeight V X,
      ∀ T : WeakSolutionScalarTest, ∀ w : zeroBoundaryGraph V X, ∀ c : ℝ,
      a ≤ b → A < a → b < B →
      W.affineEnergy T w c (v a) - W.affineEnergy T w c (v b) =
        ∫ t in Icc a b, F t (W.affineEnergyMap hX T w c (v t)) := by
  filter_upwards [hp.ae_local_spatial_energy_endpoint_identity hX,
    hp.ae_local_linear_energy_endpoint_identity] with a ha hla
  filter_upwards [ha, hla] with b hb hlb
  intro W T w c hab hAa hbB
  have hsub : Icc a b ⊆ Icc A B := fun _ ht => ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  have hF := hp.2.2.2.2.1.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hv := hp.1.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hP := W.multiplier.comp_memLp' (T.memLp_energyMap V X hX hv)
  let : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  exact affine_energy_sub_eq_integral_of_endpoint_identities hF hP w c
    (hb W T hab hAa hbB) (hlb w hab hAa hbB)

end HeatKernel

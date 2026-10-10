-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionSpatialEnergy
public import HeatKernel.Moser.WeakSolutionCutoffDualEquation
public import HeatKernel.Moser.WeakSolutionEnergyIdentityLimits

import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.NormedSpace
import all Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # Spatially weighted nonlinear identities from weak cutoff time equations

The flux at positive averaging scale remains the averaged original flux. Strong
energy and flux-pairing convergence give the spatially weighted endpoint identity
for the original curve on a common full-measure set of endpoints.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology NNReal
namespace HeatKernel

/-- Spatial and temporal weights can be used directly in the regularized weak time
equation, with no additional dual derivative hypothesis. -/
theorem WeakSolutionSpatialWeight.regularized_weighted_energy_eq_of_weak_cutoff_time_pair
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (T : WeakSolutionScalarTest)
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X} (hv : MemLp v 2 volume) {M : ℝ≥0}
    (hb : ∀ᵐ t ∂volume, ‖(v t : GradientSpace (N := N) ⊤ q).fst‖ ≤ M)
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B h a b : ℝ}
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F)
    (hh : 0 < h) (hinside : uIcc a b ⊆ Ioo A (B - h))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) :
    (∫ t in a..b, deriv χ t * W.energy T (forwardTimeAverage h v t) -
      χ t * forwardTimeAverage h F t (W.energyMap hX T (forwardTimeAverage h v t))) =
      χ b * W.energy T (forwardTimeAverage h v b) -
        χ a * W.energy T (forwardTimeAverage h v a) := by
  have hac := W.absolutelyContinuousOnInterval_energy_average T hv hb hh a b
  have hprodac : AbsolutelyContinuousOnInterval
      (fun t => χ t * W.energy T (forwardTimeAverage h v t)) a b := by
    simpa only [Pi.mul_def] using hχ.contDiffOn.absolutelyContinuousOnInterval.mul hac
  have hder := W.ae_hasDerivAt_energy_forwardTimeAverage hX T
    (hv.locallyIntegrable (by norm_num)) h
  rw [← hprodac.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hder, hp.ae_regularized_dual_time_equation hh.le] with t ht hd
  intro hm
  have hprod := ((hχ.differentiable (by norm_num) t).hasDerivAt).mul ht
  have hprod' : deriv (fun s => χ s * W.energy T (forwardTimeAverage h v s)) t =
      deriv χ t * W.energy T (forwardTimeAverage h v t) +
        χ t * zeroBoundaryValueFunctional V X (h⁻¹ • (v (t + h) - v t))
          (W.energyMap hX T (forwardTimeAverage h v t)) := by
    simpa only [Pi.mul_def] using hprod.deriv
  rw [hprod', hd (hinside (uIoc_subset_uIcc hm))]
  simp only [neg_apply, mul_neg, sub_eq_add_neg]

/-- The unregularized spatially weighted nonlinear identity holds at almost every
pair of interior times, simultaneously for all spatial weights and scalar tests. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.ae_spatial_energy_endpoint_identity
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X} (hv : MemLp v 2 volume) {M : ℝ≥0}
    (hb : ∀ᵐ t ∂volume, ‖(v t : GradientSpace (N := N) ⊤ q).fst‖ ≤ M)
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B : ℝ}
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F) :
    ∀ᵐ a ∂volume, ∀ᵐ b ∂volume, ∀ W : WeakSolutionSpatialWeight V X,
      ∀ T : WeakSolutionScalarTest, a ≤ b → A < a → b < B →
      W.energy T (v a) - W.energy T (v b) =
        ∫ t in Icc a b, F t (W.energyMap hX T (v t)) := by
  let : InnerProductSpace ℝ (zeroBoundaryGraph V X) :=
    {(inferInstance : InnerProductSpace ℝ (zeroBoundaryGraph V X)) with
      toNormedSpace := (inferInstance : NormedSpace ℝ (zeroBoundaryGraph V X))}
  have hF : MemLp F 2 (volume.restrict (Ioo A B)) :=
    hp.2.2.2.2.1.mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
  filter_upwards [ae_energy_endpoint_identity_of_regularized hv] with a ha
  filter_upwards [ha] with b hablim
  intro W T hab hAa hbB
  have hsub : Icc a b ⊆ Ioo A B := fun _ ht =>
    ⟨hAa.trans_le ht.1, ht.2.trans_lt hbB⟩
  apply hablim (Ioo A B) isOpen_Ioo F hF (W.energyMap hX T)
    (W.continuous_energyMap hX T) (‖W.multiplier‖₊ * T.bound) (W.norm_energyMap_le hX T)
    (W.energy T) (W.continuous_energy hX T) hab hsub
  refine ⟨B - b, sub_pos.mpr hbB, ?_⟩
  intro h hh
  have hinside : uIcc a b ⊆ Ioo A (B - h) := by
    rw [uIcc_of_le hab]
    intro t ht
    constructor
    · exact hAa.trans_le ht.1
    · linarith [ht.2, hh.2]
  have he := W.regularized_weighted_energy_eq_of_weak_cutoff_time_pair
    hX T hv hb hp hh.1 hinside (χ := fun _ => 1) contDiff_const
  simp only [deriv_const, zero_mul, one_mul, zero_sub, intervalIntegral.integral_neg] at he
  have he' : W.energy T (forwardTimeAverage h v a) -
      W.energy T (forwardTimeAverage h v b) =
      ∫ t in a..b, forwardTimeAverage h F t (W.energyMap hX T (forwardTimeAverage h v t)) := by
    linarith
  simpa only [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc] using he'

/-- Local square integrability and the local essential value bound already contained
in the weak cutoff pair suffice for every spatially weighted endpoint identity. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.ae_local_spatial_energy_endpoint_identity
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B : ℝ}
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F) :
    ∀ᵐ a ∂volume, ∀ᵐ b ∂volume, ∀ W : WeakSolutionSpatialWeight V X,
      ∀ T : WeakSolutionScalarTest, a ≤ b → A < a → b < B →
      W.energy T (v a) - W.energy T (v b) =
        ∫ t in Icc a b, F t (W.energyMap hX T (v t)) := by
  obtain ⟨w, hw, heq, hp', _, _, ⟨M, hM⟩, _⟩ :=
    hp.exists_extension_with_value_endpoints measurableSet_Icc
  have hid := IsZeroBoundaryWeakCutoffEnergyTimePair.ae_spatial_energy_endpoint_identity
    (N := N) (q := q) (V := V) (X := X) (coeff := coeff)
    (u := u) (g := g) (φ := φ) (k := k) (v := w) (F := F)
    (A := A) (B := B) hX hw (M := M) hM hp'
  filter_upwards [hid] with a ha
  filter_upwards [ha] with b hb
  intro W T hab hAa hbB
  have hsub : Icc a b ⊆ Icc A B := fun _ ht =>
    ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  have he := hb W T hab hAa hbB
  rw [heq (hsub ⟨le_rfl, hab⟩), heq (hsub ⟨hab, le_rfl⟩)] at he
  refine he.trans ?_
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  exact congrArg (fun z => F t (W.energyMap hX T z)) (heq (hsub ht))

end HeatKernel

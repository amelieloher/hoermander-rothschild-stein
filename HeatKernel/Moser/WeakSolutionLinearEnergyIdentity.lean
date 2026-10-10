-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionCutoffDualEquation
public import HeatKernel.Moser.WeakSolutionFixedTestLimits
public import HeatKernel.Moser.PointwiseAverageLimits
public import HeatKernel.Moser.BoundedTimeAverages

import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.NormedSpace
import all Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # Linear endpoint identities for local weak cutoff curves

Fixed spatial tests recover the affine terms removed when normalizing nonlinear
tests at zero. The weak cutoff pair supplies its dual time equation and local
square integrability. No additional time derivative hypothesis is required.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology NNReal
namespace HeatKernel

/-- The value pairing of a bounded cutoff curve has a regularized linear endpoint
identity against every fixed spatial form-domain test. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.regularized_linear_energy_eq
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X} (hv : MemLp v 2 volume) {M : ℝ≥0}
    (hb : ∀ᵐ t ∂volume, ‖(v t : GradientSpace (N := N) ⊤ q).fst‖ ≤ M)
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B h a b : ℝ}
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F)
    (hh : 0 < h) (hinside : uIcc a b ⊆ Ioo A (B - h)) (w : zeroBoundaryGraph V X) :
    zeroBoundaryValueFunctional V X (forwardTimeAverage h v a) w -
      zeroBoundaryValueFunctional V X (forwardTimeAverage h v b) w =
        ∫ t in a..b, forwardTimeAverage h F t w := by
  let L : zeroBoundaryGraph V X →L[ℝ] ℝ := (zeroBoundaryValueFunctional V X).flip w
  have hD : MemLp (L ∘ v) 2 volume := L.comp_memLp' hv
  have hDb : ∀ᵐ t ∂volume, ‖L (v t)‖ ≤
      (M * ‖(w : GradientSpace (N := N) ⊤ q).fst‖₊ : ℝ≥0) := by
    filter_upwards [hb] with t ht
    have he := norm_spatialValueFunctional_apply_le ⊤ X
      (v t : GradientSpace (N := N) ⊤ q).fst (zeroBoundaryEnergyInclusion V X w)
    exact he.trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
  have hacD := (lipschitzWith_forwardTimeAverage_of_ae_norm_le
    (hD.locallyIntegrable (by norm_num)) hDb h).lipschitzOnWith.absolutelyContinuousOnInterval
    (a := a) (b := b)
  have hac : AbsolutelyContinuousOnInterval (fun t => L (forwardTimeAverage h v t)) a b := by
    have heq : (fun t => L (forwardTimeAverage h v t)) = forwardTimeAverage h (L ∘ v) :=
      funext fun t => map_forwardTimeAverage_of_locallyIntegrable L
        (hv.locallyIntegrable (by norm_num)) h t
    rw [heq]
    exact hacD
  have hi : (∫ t in a..b, -(forwardTimeAverage h F t w)) =
      L (forwardTimeAverage h v b) - L (forwardTimeAverage h v a) := by
    rw [← hac.integral_deriv_eq_sub]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_hasDerivAt_map_forwardTimeAverage L (hv.locallyIntegrable (by norm_num)) h,
      hp.ae_regularized_dual_time_equation hh.le] with t ht hd
    intro hm
    rw [ht.deriv]
    have he := congrArg (fun D => D w) (hd (hinside (uIoc_subset_uIcc hm)))
    simpa only [L, map_smul, map_sub, ContinuousLinearMap.flip_apply,
      smul_apply, sub_apply, neg_apply] using he.symm
  rw [intervalIntegral.integral_neg] at hi
  change -(∫ t in a..b, forwardTimeAverage h F t w) =
    zeroBoundaryValueFunctional V X (forwardTimeAverage h v b) w -
      zeroBoundaryValueFunctional V X (forwardTimeAverage h v a) w at hi
  linarith

/-- The unregularized linear endpoint identity holds on one common full-measure
set for every fixed spatial form-domain test. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.ae_linear_energy_endpoint_identity
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X} (hv : MemLp v 2 volume) {M : ℝ≥0}
    (hb : ∀ᵐ t ∂volume, ‖(v t : GradientSpace (N := N) ⊤ q).fst‖ ≤ M)
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B : ℝ}
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F) :
    ∀ᵐ a ∂volume, ∀ᵐ b ∂volume, ∀ w : zeroBoundaryGraph V X,
      a ≤ b → A < a → b < B →
      zeroBoundaryValueFunctional V X (v a) w - zeroBoundaryValueFunctional V X (v b) w =
        ∫ t in Icc a b, F t w := by
  let : InnerProductSpace ℝ (zeroBoundaryGraph V X) :=
    {(inferInstance : InnerProductSpace ℝ (zeroBoundaryGraph V X)) with
      toNormedSpace := (inferInstance : NormedSpace ℝ (zeroBoundaryGraph V X))}
  have hlim := ae_tendsto_forwardTimeAverage (hv.locallyIntegrable (by norm_num))
  have hF : MemLp F 2 (volume.restrict (Ioo A B)) :=
    hp.2.2.2.2.1.mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
  filter_upwards [hlim] with a ha
  filter_upwards [hlim] with b hb'
  intro w hab hAa hbB
  let L : zeroBoundaryGraph V X →L[ℝ] ℝ := (zeroBoundaryValueFunctional V X).flip w
  have henergy := (L.continuous.continuousAt.tendsto.comp ha).sub
    (L.continuous.continuousAt.tendsto.comp hb')
  have hsub : Icc a b ⊆ Ioo A B := fun _ ht => ⟨hAa.trans_le ht.1, ht.2.trans_lt hbB⟩
  have hflux := tendsto_integral_forwardTimeAverage_fixed_test isOpen_Ioo isCompact_Icc hsub hF w
  apply tendsto_nhds_unique henergy (hflux.congr' ?_)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (sub_pos.mpr hbB)).filter_mono inf_le_left] with h hh hsmall
  have hinside : uIcc a b ⊆ Ioo A (B - h) := by
    rw [uIcc_of_le hab]
    intro t ht
    exact ⟨hAa.trans_le ht.1, by linarith [ht.2]⟩
  have he := hp.regularized_linear_energy_eq hv hb hh hinside w
  simpa only [Function.comp_def, L, ContinuousLinearMap.flip_apply, intervalIntegral.integral_of_le hab,
    integral_Icc_eq_integral_Ioc] using he.symm

/-- A local weak cutoff pair has a bounded global extension which agrees on the
entire compact time interval. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.exists_bounded_extension_eqOn
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B : ℝ}
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F) :
    ∃ (v' : ℝ → zeroBoundaryGraph V X) (M : ℝ≥0), MemLp v' 2 volume ∧
      (∀ᵐ t ∂volume, ‖(v' t : GradientSpace (N := N) ⊤ q).fst‖ ≤ M) ∧
      EqOn v' v (Icc A B) ∧
      IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v' F := by
  obtain ⟨v', hv', heq, hp', _, _, ⟨M, hM⟩, _⟩ :=
    hp.exists_extension_with_value_endpoints measurableSet_Icc
  exact ⟨v', M, hv', hM, heq, hp'⟩

/-- The local square integrability and essential value bound in the weak cutoff
pair suffice for all fixed-test endpoint identities. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.ae_local_linear_energy_endpoint_identity
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B : ℝ}
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F) :
    ∀ᵐ a ∂volume, ∀ᵐ b ∂volume, ∀ w : zeroBoundaryGraph V X,
      a ≤ b → A < a → b < B →
      zeroBoundaryValueFunctional V X (v a) w - zeroBoundaryValueFunctional V X (v b) w =
        ∫ t in Icc a b, F t w := by
  obtain ⟨v', M, hv', hM, heq, hp'⟩ := hp.exists_bounded_extension_eqOn
  have hid := IsZeroBoundaryWeakCutoffEnergyTimePair.ae_linear_energy_endpoint_identity
    (N := N) (q := q) (V := V) (X := X) (coeff := coeff) (u := u) (g := g)
    (φ := φ) (k := k) (v := v') (F := F) (A := A) (B := B) hv' hM hp'
  exact ae_linear_endpoint_identity_of_eqOn (zeroBoundaryValueFunctional V X) heq hid

end HeatKernel

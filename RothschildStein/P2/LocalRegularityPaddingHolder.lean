-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityPaddingSetup
public import RothschildStein.P1.PaddingHolderAmbientNorm
public import RothschildStein.P1.PaddingNoDriftHolderAmbientNorm
public import RothschildStein.P1.PaddingHolderAmbientDescent
public import RothschildStein.P1.PaddingNoDriftHolderAmbientDescent
public import RothschildStein.P1.PaddingDriftHolderLift
public import RothschildStein.P1.PaddingNoDriftHolderLift
public import RothschildStein.P1.PaddingDriftHolderPullbackNorm
public import RothschildStein.P1.PaddingNoDriftHolderPullbackNorm
public import RothschildStein.P1.PaddingDriftHolderAlphabet
public import RothschildStein.P1.PaddingNoDriftHolderAlphabet
public import RothschildStein.P1.PaddingHolderDescent
public import RothschildStein.P1.PaddingNoDriftHolderDescent
public import RothschildStein.P1.PaddingContinuousSlice
public import RothschildStein.P1.IntrinsicWordInputCongruence
public import RothschildStein.P1.ZeroFieldIntrinsicWords
public import RothschildStein.S.IntrinsicUniqueness

/-!
# Local regularity assembly: the Hölder descent from the padded system

Auxiliary facts for `rs3_no_drift_holder_of_hypotheses` and `rs3_drift_holder_of_hypotheses`:

* `slice_eq_of_continuous`: a continuous representative of the padded tensor is independent of the
  fiber coordinate;
* `eLpNorm_top_cylinder_le`: the sup norm of a function of the base variable on a cylinder;
* `eqOn_zero_of_added_pair_noDrift/_drift`: the second intrinsic derivative of a function of the
  base variable along an added diffusion `∂_{z_j}` vanishes, so the added terms drop out of the
  padded equation `∑ᵢ XᵢXᵢ u + ∑ⱼ ∂_{z_j}² u = f`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2

section Slices

variable {n d : ℕ}

/-- A continuous representative `v` of the padded tensor of `T` on the cylinder `Ω × J` is
independent of the fiber coordinate: `v (x, z) = v (x, z₀)` for `x ∈ Ω`, `z, z₀ ∈ J`. -/
theorem slice_eq_of_continuous (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (hJ : volume (J : Set (Fin d → ℝ)) ≠ ⊤) (η : TestFunction J ℝ (⊤ : ℕ∞))
    (hη : ∫ z, η z = 1) (T : Distribution Ω ℝ (⊤ : ℕ∞)) (v : (Fin (n + d) → ℝ) → ℝ)
    (hv : LocallyIntegrableOn v (cylinder Ω J : Set (Fin (n + d) → ℝ)) volume)
    (hT : paddingDistributionTensorOneCLM Ω (cylinder Ω J) (padding_cylinder_subset_base Ω J) T =
      Distribution.ofFun (cylinder Ω J) v volume (⊤ : ℕ∞))
    (hc : ContinuousOn v (cylinder Ω J : Set (Fin (n + d) → ℝ)))
    {x : Fin n → ℝ} (hx : x ∈ (Ω : Set (Fin n → ℝ))) {z z₀ : Fin d → ℝ}
    (hz : z ∈ (J : Set (Fin d → ℝ))) (hz₀ : z₀ ∈ (J : Set (Fin d → ℝ))) :
    v (joinPoint x z) = v (joinPoint x z₀) := by
  obtain ⟨-, hae⟩ := paddingDistributionTensor_descent Ω J hJ η hη T v hv hT
  exact (fiberAvg_eq_slice hc hae hη hx hz).symm.trans (fiberAvg_eq_slice hc hae hη hx hz₀)

/-- The sup norm of a function of the base variable on a cylinder is at most the sup norm of the
function on the base. -/
theorem eLpNorm_top_cylinder_le (W : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (u : (Fin n → ℝ) → ℝ) (v : (Fin (n + d) → ℝ) → ℝ)
    (hv : ∀ ξ ∈ (cylinder W J : Set (Fin (n + d) → ℝ)), v ξ = u (basePoint ξ)) :
    eLpNorm v ⊤ (volume.restrict (cylinder W J : Set (Fin (n + d) → ℝ))) ≤
      eLpNorm u ⊤ (volume.restrict (W : Set (Fin n → ℝ))) := by
  have h : v =ᵐ[volume.restrict (cylinder W J : Set (Fin (n + d) → ℝ))]
      fun ξ => u (basePoint ξ) := ae_restrict_of_forall_mem (cylinder W J).isOpen.measurableSet hv
  rw [eLpNorm_congr_ae h]
  exact eLpNorm_top_comp_basePoint_le (cylinder W J).isOpen.measurableSet
    W.isOpen.measurableSet (fun ξ hξ => hξ.1) u

/-- A function of the base variable that is continuous on `Ω` is locally integrable on a cylinder
over `Ω`. -/
theorem locallyIntegrableOn_comp_basePoint_cylinder (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f (Ω : Set (Fin n → ℝ))) :
    LocallyIntegrableOn (fun ξ => f (basePoint ξ)) (cylinder Ω J : Set (Fin (n + d) → ℝ))
      volume :=
  (hf.comp continuous_basePoint.continuousOn fun _ hξ => hξ.1).locallyIntegrableOn
    (cylinder Ω J).isOpen.measurableSet

/-- The slice `x ↦ v (x, 0)` of a function on the cylinder is continuous on the base if `v` is. -/
theorem continuousOn_slice (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ)) {z : Fin d → ℝ}
    (hz : z ∈ (J : Set (Fin d → ℝ))) {v : (Fin (n + d) → ℝ) → ℝ}
    (hv : ContinuousOn v (cylinder Ω J : Set (Fin (n + d) → ℝ))) :
    ContinuousOn (fun x => v (joinPoint x z)) (Ω : Set (Fin n → ℝ)) :=
  hv.comp (continuous_joinPoint_left z).continuousOn fun _ hx => joinPoint_mem_cylinder.2 ⟨hx, hz⟩

end Slices

section Added

variable {q n d : ℕ}

/-- Any function has zero second intrinsic derivative along an added field, in the projected
no-drift alphabet. -/
theorem hasIntrinsicWordDeriv_addedPair_noDrift (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (u : (Fin n → ℝ) → ℝ) (j : Fin d) :
    hasIntrinsicWordDeriv (paddingNoDriftBaseAlphabet (d := d) X) Ω
      [Fin.natAdd q j, Fin.natAdd q j] u (fun _ => 0) := by
  have hz : paddingNoDriftBaseAlphabet (d := d) X (Fin.natAdd q j) = fun _ => 0 := by
    simp [paddingNoDriftBaseAlphabet, Pi.zero_def]
  refine ⟨fun _ => 0, ⟨u, fun _ _ => rfl, ?_⟩, ?_⟩
  · rw [hz]
    exact hasIntrinsicDeriv_zero_field Ω u
  · rw [hz]
    exact hasIntrinsicDeriv_zero_field Ω _

/-- Any function has zero second intrinsic derivative along an added field, in the projected drift
alphabet. -/
theorem hasIntrinsicWordDeriv_addedPair_drift (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) (u : (Fin n → ℝ) → ℝ) (j : Fin d) :
    hasIntrinsicWordDeriv (paddingDriftBaseAlphabet (d := d) X) Ω
      [(Fin.natAdd q j).succ, (Fin.natAdd q j).succ] u (fun _ => 0) := by
  have hz : paddingDriftBaseAlphabet (d := d) X (Fin.natAdd q j).succ = fun _ => 0 := by
    simp [paddingDriftBaseAlphabet, Pi.zero_def]
  refine ⟨fun _ => 0, ⟨u, fun _ _ => rfl, ?_⟩, ?_⟩
  · rw [hz]
    exact hasIntrinsicDeriv_zero_field Ω u
  · rw [hz]
    exact hasIntrinsicDeriv_zero_field Ω _

/-- If `v = u ∘ π` on the cylinder, the padded intrinsic second derivative of `v` along an added
diffusion `∂_{z_j}` is zero (no drift). -/
theorem eqOn_zero_of_added_pair_noDrift (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ))) (u : (Fin n → ℝ) → ℝ)
    (v g : (Fin (n + d) → ℝ) → ℝ) (j : Fin d)
    (hv : EqOn v (fun ξ => u (basePoint ξ)) (cylinder Ω J : Set (Fin (n + d) → ℝ)))
    (hg : hasIntrinsicWordDeriv (paddingNoDriftVectorFields (d := d) X) (cylinder Ω J)
      [Fin.natAdd q j, Fin.natAdd q j] v g) :
    EqOn g (fun _ => 0) (cylinder Ω J : Set (Fin (n + d) → ℝ)) := by
  have h0 := hasIntrinsicWordDeriv_paddingNoDrift_lift Ω J X hX [Fin.natAdd q j, Fin.natAdd q j]
    u (fun _ => 0) (hasIntrinsicWordDeriv_addedPair_noDrift Ω X u j)
  have h0' := hasIntrinsicWordDeriv_congr_input (cylinder Ω J) _ _ (fun ξ hξ => (hv hξ).symm) h0
  exact RothschildStein.S.hasIntrinsicWordDeriv_unique (cylinder Ω J) _ _ hg h0'

/-- If `v = u ∘ π` on the cylinder, the padded intrinsic second derivative of `v` along an added
diffusion `∂_{z_j}` is zero (drift). -/
theorem eqOn_zero_of_added_pair_drift (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ))) (u : (Fin n → ℝ) → ℝ)
    (v g : (Fin (n + d) → ℝ) → ℝ) (j : Fin d)
    (hv : EqOn v (fun ξ => u (basePoint ξ)) (cylinder Ω J : Set (Fin (n + d) → ℝ)))
    (hg : hasIntrinsicWordDeriv (paddingVectorFields (d := d) X) (cylinder Ω J)
      [(Fin.natAdd q j).succ, (Fin.natAdd q j).succ] v g) :
    EqOn g (fun _ => 0) (cylinder Ω J : Set (Fin (n + d) → ℝ)) := by
  have h0 := hasIntrinsicWordDeriv_paddingDrift_lift Ω J X hX
    [(Fin.natAdd q j).succ, (Fin.natAdd q j).succ] u (fun _ => 0)
    (hasIntrinsicWordDeriv_addedPair_drift Ω X u j)
  have h0' := hasIntrinsicWordDeriv_congr_input (cylinder Ω J) _ _ (fun ξ hξ => (hv hξ).symm) h0
  exact RothschildStein.S.hasIntrinsicWordDeriv_unique (cylinder Ω J) _ _ hg h0'

end Added

end RothschildStein.P2

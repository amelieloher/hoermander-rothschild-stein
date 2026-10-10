-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionPositivePartInterface
public import HeatKernel.Bridge.SquareIntegrableSlices
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! Spatial extension by zero for the representatives in backward energy estimates. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Extending the value and gradient by zero outside a set containing the cutoff
and all its derivatives preserves the full dual time equation. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.indicator_representatives {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ} {J : Set ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X} {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)}
    (h : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff J u g φ k v F)
    {K : Set (Fin N → ℝ)} (hφ : ∀ x ∉ K, φ x = 0)
    (hk : ∀ i x, x ∉ K → k i x = 0) :
    IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff J
      (fun t => K.indicator (u t)) (fun i t => K.indicator (g i t)) φ k v F := by
  classical
  rcases h with ⟨hv, hbound, hvalue, hgradient, hF, hflux, htime⟩
  refine ⟨hv, hbound, ?_, ?_, hF, ?_, htime⟩
  · filter_upwards [hvalue] with t ht
    apply ht.trans
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ K
      · simp only [indicator_of_mem hx]
      · simp only [indicator_of_notMem hx, hφ x hx, mul_zero]
  · intro i
    filter_upwards [hgradient i] with t ht
    apply ht.trans
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ K
      · simp only [indicator_of_mem hx]
      · simp only [indicator_of_notMem hx, hφ x hx, hk i x hx, mul_zero]
  · filter_upwards [hflux] with t ht
    intro w
    rw [ht w]
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ K
      · simp only [indicator_of_mem hx]
      · simp only [indicator_of_notMem hx, hφ x hx, hk i x hx, zero_mul,
          zero_add, mul_zero]

/-- Compact-cylinder bounds for the common weak gradient give global spatial
square-integrable slices for both extended representatives. -/
theorem WeakSolutionEnergyInterface.memLp_indicator_representatives {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (h : WeakSolutionEnergyInterface X coeff I U u g)
    (hu : AEStronglyMeasurable (Function.uncurry u)
      (volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))))
    {J : Set ℝ} {K : Set (Fin N → ℝ)}
    (hJ : IsCompact J) (hJI : J ⊆ (I : Set ℝ))
    (hK : IsCompact K) (hKU : K ⊆ (U : Set (Fin N → ℝ))) :
    MemLp (fun z : ℝ × (Fin N → ℝ) => K.indicator (u z.1) z.2) 2
        ((volume.restrict J).prod volume) ∧
      (∀ i, MemLp (fun z : ℝ × (Fin N → ℝ) => K.indicator (g i z.1) z.2) 2
        ((volume.restrict J).prod volume)) ∧
      ∀ᵐ t ∂volume.restrict J, MemLp (K.indicator (u t)) 2 volume ∧
        ∀ i, MemLp (K.indicator (g i t)) 2 volume := by
  have hv := memLp_two_spatial_zero_extension hK.measurableSet
    (h.memLp_value_on_compact_cylinder hu hJ hJI hK hKU)
  have hg (i : Fin q) : MemLp
      (fun z : ℝ × (Fin N → ℝ) => K.indicator (g i z.1) z.2) 2
      ((volume.restrict J).prod volume) := by
    apply memLp_two_spatial_zero_extension (f := fun z => g i z.1 z.2) hK.measurableSet
    simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using
      (h.local_bounds J K hJ hJI hK hKU).2 i
  refine ⟨hv, hg, ?_⟩
  filter_upwards [ae_memLp_two_slice hv, ae_all_iff.mpr (fun i => ae_memLp_two_slice (hg i))]
    with t ht hgt
  exact ⟨ht, hgt⟩

end HeatKernel

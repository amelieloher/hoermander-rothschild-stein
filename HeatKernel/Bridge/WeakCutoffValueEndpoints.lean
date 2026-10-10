-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.WeakCutoffPairCongruence
public import HeatKernel.Moser.CutoffAveragedChainRule
public import HeatKernel.Moser.NonlinearAverageEndpointProperty
public import HeatKernel.Moser.BoundedSquareIntegrableExtensions
import Mathlib.Tactic

/-! # Nonlinear value endpoints for compatible weak cutoff energy curves -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped NNReal ENNReal
namespace HeatKernel

/-- One global extension preserves the actual zero-boundary energy pair on its
time set and gives both the energy averaged chain rule and the weighted nonlinear
endpoint identities for its bounded spatial L² value curve. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.exists_extension_with_value_endpoints
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ} {J : Set ℝ} (hJ : MeasurableSet J)
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X} {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)}
    (h : IsZeroBoundaryWeakCutoffEnergyTimePair V X a J u g φ k v F) :
    ∃ w : ℝ → zeroBoundaryGraph V X,
      MemLp w 2 volume ∧ EqOn w v J ∧
      IsZeroBoundaryWeakCutoffEnergyTimePair V X a J u g φ k w F ∧
      SatisfiesWeightedAverageChainRule w ∧
      MemLp (fun t => (w t : GradientSpace (N := N) ⊤ q).fst) 2 volume ∧
      (∃ M : ℝ≥0, ∀ᵐ t ∂volume, ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ≤ M) ∧
      HasWeightedNonlinearAverageEndpoints
        (fun t => (w t : GradientSpace (N := N) ⊤ q).fst) := by
  classical
  let w := J.indicator v
  have hw : MemLp w 2 volume := (memLp_indicator_iff_restrict hJ).mpr h.1
  have he : EqOn w v J := fun t ht => indicator_of_mem ht v
  have heq : v =ᵐ[volume.restrict J] w := by
    filter_upwards [ae_restrict_mem hJ] with t ht
    exact (he ht).symm
  let P : zeroBoundaryGraph V X →L[ℝ] SpatialL2 (N := N) ⊤ :=
    (energyInclusion ⊤ X).comp (zeroBoundaryEnergyInclusion V X)
  have hval : MemLp (P ∘ w) 2 volume := P.comp_memLp' hw
  have hb : essSup (fun t => eLpNorm ((P ∘ v) t) 2
      (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))))
      (volume.restrict J) < ⊤ := by
    change essSup (fun t => eLpNorm ((v t : GradientSpace (N := N) ⊤ q).fst) 2
      (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))))
      (volume.restrict J) < ⊤
    simpa only [Opens.coe_top, Measure.restrict_univ] using h.2.1
  obtain ⟨M, hM⟩ := exists_ae_norm_le_of_essSup_eLpNorm_lt_top (P ∘ v) hb
  have hglobal : ∀ᵐ t ∂volume, ‖(P ∘ w) t‖ ≤ M := by
    filter_upwards [(ae_restrict_iff' hJ).mp hM] with t ht
    by_cases htJ : t ∈ J
    · simpa only [Function.comp_apply, w, indicator_of_mem htJ] using ht htJ
    · simp only [Function.comp_apply, w, indicator_of_notMem htJ, map_zero, norm_zero]
      exact M.coe_nonneg
  have hchain : SatisfiesWeightedAverageChainRule w := by
    intro δ Φ hΦ χ hχ
    exact ae_hasDerivAt_weighted_comp_forwardTimeAverage
      (hw.locallyIntegrable (by norm_num)) δ hΦ hχ
  exact ⟨w, hw, he, h.congr heq ae_eq_rfl, hchain, hval, ⟨M, hglobal⟩,
    hasWeightedNonlinearAverageEndpoints_of_bounded_memLp hval hglobal⟩

end HeatKernel

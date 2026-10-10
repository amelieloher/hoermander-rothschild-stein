-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.CompatibleParabolicEnergyWitness
public import HeatKernel.Bridge.AlmostEverywhereSupportedPairings
public import HeatKernel.Sobolev.ZeroBoundarySupport
public import HeatKernel.Bridge.ParabolicValueIntegrability
public import HeatKernel.Bridge.LocalizedDualValueCurves
public import HeatKernel.Bridge.ParabolicDualFluxCurves
public import HeatKernel.Bridge.DualStationaryTimeBalance
public import HeatKernel.Bridge.DualTimeBalance
public import HeatKernel.Bridge.ParabolicCoefficientBounds
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic

/-! # Compatible local dual-valued time balances for weak solutions -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Dual representations of the value and flux convert the stationary test
identity into a Bochner weak time balance. -/
theorem HasStationaryEnergyTestIdentity.dual_time_balance {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (he : HasStationaryEnergyTestIdentity X a I U u g)
    {J : Set ℝ} {K : Set (Fin N → ℝ)}
    (hJ : IsCompact J) (hJI : J ⊆ (I : Set ℝ))
    (hK : IsCompact K) (hKU : K ⊆ (U : Set (Fin N → ℝ)))
    (V : Opens (Fin N → ℝ)) (hVK : (V : Set (Fin N → ℝ)) ⊆ K)
    (D F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ))
    (hD : MemLp D 2 (volume.restrict J)) (hF : MemLp F 2 (volume.restrict J))
    (hDr : ∀ᵐ t ∂volume.restrict J, ∀ v : zeroBoundaryGraph V X,
      D t v = ∫ x, u t x * (v : GradientSpace (N := N) ⊤ q).fst x)
    (hFr : ∀ᵐ t ∂volume.restrict J, ∀ v : zeroBoundaryGraph V X,
      F t v = ∑ i, ∫ x, (∑ j, a t x i j * g j t x) *
        (v : GradientSpace (N := N) ⊤ q).snd i x) :
    SatisfiesDualTimeBalance J D F := by
  apply satisfiesDualTimeBalance_of_memLp_of_eval hJ hD hF
  intro ψ hψ hcψ hsψ v
  obtain ⟨hi, hf, hid⟩ := he.time_balance_of_dual_flux
    hJ hJI hK hKU V hVK F hFr hψ hcψ hsψ v
  have hd : (fun t => deriv ψ t * ∫ x, u t x * (v : GradientSpace (N := N) ⊤ q).fst x)
      =ᵐ[volume.restrict J] (fun t => deriv ψ t * D t v) := by
    filter_upwards [hDr] with t ht
    rw [ht v]
  exact ⟨hi.congr hd, hf, (integral_congr_ae hd).symm.trans hid⟩

end HeatKernel

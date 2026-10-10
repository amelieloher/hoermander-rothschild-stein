-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.StationaryTimeBalance
public import HeatKernel.Bridge.ZeroBoundaryDualRestriction
import Mathlib.Tactic

/-! # Stationary weak time balances written with dual-valued fluxes -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- A dual curve representing the spatial flux rewrites every stationary weak
 time balance as the integral pairing with that dual curve. -/
theorem HasStationaryEnergyTestIdentity.time_balance_of_dual_flux {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (he : HasStationaryEnergyTestIdentity X a I U u g)
    {J : Set ℝ} {K : Set (Fin N → ℝ)}
    (hJ : IsCompact J) (hJI : J ⊆ (I : Set ℝ))
    (hK : IsCompact K) (hKU : K ⊆ (U : Set (Fin N → ℝ)))
    (V : Opens (Fin N → ℝ)) (hVK : (V : Set (Fin N → ℝ)) ⊆ K)
    (F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ))
    (hF : ∀ᵐ t ∂volume.restrict J, ∀ v : zeroBoundaryGraph V X,
      F t v = ∑ i, ∫ x, (∑ j, a t x i j * g j t x) *
        (v : GradientSpace (N := N) ⊤ q).snd i x)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ J) (v : zeroBoundaryGraph V X) :
    Integrable (fun t => deriv ψ t * ∫ x, u t x * (v : GradientSpace (N := N) ⊤ q).fst x)
      (volume.restrict J) ∧
    Integrable (fun t => ψ t * F t v) (volume.restrict J) ∧
    (∫ t in J, deriv ψ t * ∫ x, u t x * (v : GradientSpace (N := N) ⊤ q).fst x) =
      ∫ t in J, ψ t * F t v := by
  obtain ⟨hi, hf, hid⟩ := he.time_balance hJ hJI hK hKU V hVK hψ hcψ hsψ v
  have heq : (fun t => ∑ i, ψ t * ∫ x, (∑ j, a t x i j * g j t x) *
      (v : GradientSpace (N := N) ⊤ q).snd i x) =ᵐ[volume.restrict J]
      (fun t => ψ t * F t v) := by
    filter_upwards [hF] with t ht
    rw [ht v, Finset.mul_sum]
  have hs := integrable_finsetSum Finset.univ (fun i _ => hf i)
  refine ⟨hi, hs.congr heq, ?_⟩
  rw [← integral_finsetSum Finset.univ (fun i _ => hf i)] at hid
  exact hid.trans (integral_congr_ae heq)

end HeatKernel

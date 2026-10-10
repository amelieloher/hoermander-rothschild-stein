-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.ZeroBoundaryWeakCutoffTimeIdentity
import Mathlib.Tactic.Linter

/-! # Representative changes of weak cutoff time pairs -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Almost-everywhere changes of the energy and flux curves preserve their literal
cutoff representatives and weak dual time equation. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.congr {N q : ℕ}
    {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ} {J : Set ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v w : ℝ → zeroBoundaryGraph V X} {F H : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)}
    (h : IsZeroBoundaryWeakCutoffEnergyTimePair V X a J u g φ k v F)
    (hvw : v =ᵐ[volume.restrict J] w) (hFH : F =ᵐ[volume.restrict J] H) :
    IsZeroBoundaryWeakCutoffEnergyTimePair V X a J u g φ k w H := by
  obtain ⟨hv, hb, hvalue, hgrad, hF, hflux, htime⟩ := h
  have hnorm : (fun t => eLpNorm ((v t : GradientSpace (N := N) ⊤ q).fst) 2 volume)
      =ᵐ[volume.restrict J]
      (fun t => eLpNorm ((w t : GradientSpace (N := N) ⊤ q).fst) 2 volume) :=
    hvw.fun_comp (fun z => eLpNorm ((z : GradientSpace (N := N) ⊤ q).fst) 2 volume)
  refine ⟨hv.ae_eq hvw, ?_, ?_, ?_, hF.ae_eq hFH, ?_, ?_⟩
  · rwa [← essSup_congr_ae hnorm]
  · filter_upwards [hvw, hvalue] with t ht he
    rwa [← ht]
  · intro i
    filter_upwards [hvw, hgrad i] with t ht he
    rwa [← ht]
  · filter_upwards [hFH, hflux] with t ht he
    rwa [← ht]
  · exact htime.congr (hvw.fun_comp (zeroBoundaryValueFunctional V X)) hFH

end HeatKernel

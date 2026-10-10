-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.ZeroBoundaryWeakCutoffTimeIdentity
public import HeatKernel.Bridge.ZeroBoundaryCutoffRepresentatives
public import HeatKernel.Bridge.DualTimePrecomposition
import Mathlib.Tactic.Linter

/-! # Zero-boundary realizations of weak-cutoff energy time equations -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- A compactly supported cutoff energy pair has a zero-boundary realization.
The value-gradient pair is preserved and the dual flux is restricted to the
same zero-boundary test space. -/
theorem IsWeakCutoffEnergyTimePair.exists_zeroBoundary_realization {N q : ℕ}
    (V : Opens (Fin N → ℝ))
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ} {J : Set ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ} (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (V : Set (Fin N → ℝ)))
    {v : ℝ → energyGraph (N := N) ⊤ X}
    {F : ℝ → (energyGraph (N := N) ⊤ X →L[ℝ] ℝ)}
    (h : IsWeakCutoffEnergyTimePair X a J u g φ k v F) :
    ∃ (w : ℝ → zeroBoundaryGraph V X)
      (F' : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)),
      IsZeroBoundaryWeakCutoffEnergyTimePair V X a J u g φ k w F' := by
  obtain ⟨hv, hvb, hvf, hvg, hF, hFr, ht⟩ := h
  obtain ⟨w, hw, he⟩ := exists_zeroBoundary_cutoff_curve V X hX v hv hc hs hvf
  have hval : (fun t => spatialValueFunctional ⊤ X (v t : GradientSpace (N := N) ⊤ q).fst)
      =ᵐ[volume.restrict J]
      (fun t => spatialValueFunctional ⊤ X (w t : GradientSpace (N := N) ⊤ q).fst) := by
    filter_upwards [he] with t ht
    rw [ht]
  have htime := (ht.congr hval Filter.EventuallyEq.rfl).precompose
    (zeroBoundaryEnergyInclusion V X)
  change SatisfiesDualTimeBalance J (fun t => zeroBoundaryValueFunctional V X (w t))
    (fun t => zeroBoundaryDualRestriction V X (F t)) at htime
  refine ⟨w, fun t => zeroBoundaryDualRestriction V X (F t), hw, ?_, ?_, ?_,
    memLp_zeroBoundaryDualRestriction V X hF, ?_, htime⟩
  · have heq : (fun t => eLpNorm ((w t : GradientSpace (N := N) ⊤ q).fst) 2 volume)
        =ᵐ[volume.restrict J]
        (fun t => eLpNorm ((v t : GradientSpace (N := N) ⊤ q).fst) 2 volume) := by
      filter_upwards [he] with t ht
      rw [ht]
    rw [essSup_congr_ae heq]
    exact hvb
  · filter_upwards [he, hvf] with t ht hf
    simpa only [ht] using hf
  · intro i
    filter_upwards [he, hvg i] with t ht hi
    simpa only [ht] using hi
  · filter_upwards [hFr] with t ht
    intro z
    exact ht (zeroBoundaryEnergyInclusion V X z)

/-- Compatible cutoff time curves can be realized in every zero-boundary domain
containing the cutoff support, retaining their specified weak gradient. -/
theorem HasWeakCutoffEnergyTimeCurves.hasZeroBoundaryWeakCutoffEnergyTimeCurves {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (h : HasWeakCutoffEnergyTimeCurves X a I U u g) :
    HasZeroBoundaryWeakCutoffEnergyTimeCurves X a I U u g := by
  intro J hJ hJI V φ k hφ hk C L hC hL hb hkb hc hsU hsV
  obtain ⟨v, F, hp⟩ := h J hJ hJI φ k hφ hk C L hC hL hb hkb hc hsU
  exact hp.exists_zeroBoundary_realization V hX hc hsV

end HeatKernel
